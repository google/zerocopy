#!/usr/bin/env python3
"""Executable state-space & invariant probes for multi-runtime FFI hazards.

Verifies five formal models grounded in real-world runtime architectures:
  A. Cross-heap cycle leaks (isolated RC <-> Tracing GC) vs. V8/Oilpan-style
     unified cross-boundary trace-forwarding and cross-heap write barriers.
  B. Go cgo transitive pointer-passing rules, struct-field vs. slice-backing
     granularity, shallow runtime.Pinner semantics, and Pinner leak panic.
  C. Reentrant FFI callback violating Rust &mut/noalias exclusivity vs.
     borrow-token guards and revocable generational handle indirection.
  D. GIL x native-mutex ABBA deadlock exhaustion vs. PyO3 detach-before-lock,
     and CPython 3.13t suspendable critical-section torn-invariant witness.
  E. POSIX single-slot SIGSEGV/SIGURG handler collisions and libjsig chaining.

Standard library only; requires Python 3.10+.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field
from typing import Callable


# =============================================================================
# Model A: Cross-Heap Reference Cycles vs. Unified Cross-Boundary Tracing
# =============================================================================

@dataclass
class HeapNode:
    node_id: str
    domain: str  # "GC" or "RC" (or "CPPGC" in unified mode)
    edges: list[str] = field(default_factory=list)
    weak_edges: list[str] = field(default_factory=list)


class IsolatedMultiHeap:
    """Models an independent mark-sweep GC heap paired with an independent RC heap.

    Each runtime treats incoming edges from the foreign heap as opaque external
    strong roots (e.g., JNI GlobalRef / Py<T> / Rust Arc held by a GC wrapper).
    """

    def __init__(self) -> None:
        self.gc_nodes: dict[str, HeapNode] = {}
        self.rc_nodes: dict[str, HeapNode] = {}
        self.gc_roots: set[str] = set()
        self.rc_roots: set[str] = set()

    def add_node(self, node_id: str, domain: str) -> None:
        assert domain in ("GC", "RC")
        node = HeapNode(node_id=node_id, domain=domain)
        if domain == "GC":
            self.gc_nodes[node_id] = node
        else:
            self.rc_nodes[node_id] = node

    def add_edge(self, src: str, dst: str, weak: bool = False) -> None:
        node = self.gc_nodes.get(src) or self.rc_nodes[src]
        if weak:
            node.weak_edges.append(dst)
        else:
            node.edges.append(dst)

    def _rc_refcount(self, node_id: str) -> int:
        count = 1 if node_id in self.rc_roots else 0
        for n in self.rc_nodes.values():
            count += n.edges.count(node_id)
        for n in self.gc_nodes.values():
            count += n.edges.count(node_id)
        return count

    def collect_rc_step(self) -> list[str]:
        reclaimed: list[str] = []
        changed = True
        while changed:
            changed = False
            for nid in list(self.rc_nodes):
                if self._rc_refcount(nid) == 0:
                    del self.rc_nodes[nid]
                    reclaimed.append(nid)
                    changed = True
        return reclaimed

    def collect_gc_step(self) -> list[str]:
        external_roots = {
            dst
            for n in self.rc_nodes.values()
            for dst in n.edges
            if dst in self.gc_nodes
        }
        marked: set[str] = set()
        work = deque(self.gc_roots | external_roots)
        while work:
            cur = work.popleft()
            if cur in marked or cur not in self.gc_nodes:
                continue
            marked.add(cur)
            for dst in self.gc_nodes[cur].edges:
                if dst in self.gc_nodes and dst not in marked:
                    work.append(dst)
        reclaimed = [nid for nid in list(self.gc_nodes) if nid not in marked]
        for nid in reclaimed:
            del self.gc_nodes[nid]
        return reclaimed

    def collect_to_fixpoint(self) -> tuple[list[str], int]:
        all_reclaimed: list[str] = []
        rounds = 0
        while True:
            rounds += 1
            r1 = self.collect_rc_step()
            r2 = self.collect_gc_step()
            all_reclaimed.extend(r1)
            all_reclaimed.extend(r2)
            if not r1 and not r2:
                break
        return all_reclaimed, rounds


class UnifiedCrossComponentHeap:
    """Models V8 + Blink Oilpan (CppHeap) unified cross-boundary tracing."""

    def __init__(self) -> None:
        self.nodes: dict[str, HeapNode] = {}
        self.roots: set[str] = set()
        self.color: dict[str, str] = {}

    def add_node(self, node_id: str, domain: str) -> None:
        assert domain in ("V8", "CPPGC")
        self.nodes[node_id] = HeapNode(node_id=node_id, domain=domain)

    def add_edge(self, src: str, dst: str, weak: bool = False) -> None:
        if weak:
            self.nodes[src].weak_edges.append(dst)
        else:
            self.nodes[src].edges.append(dst)

    def unified_gc(self) -> list[str]:
        self.color = {nid: "WHITE" for nid in self.nodes}
        v8_worklist: deque[str] = deque()
        cpp_worklist: deque[str] = deque()

        def mark_and_push(nid: str) -> None:
            if nid not in self.nodes or self.color[nid] != "WHITE":
                return
            self.color[nid] = "GREY"
            if self.nodes[nid].domain == "V8":
                v8_worklist.append(nid)
            else:
                cpp_worklist.append(nid)

        for r in sorted(self.roots):
            mark_and_push(r)

        while v8_worklist or cpp_worklist:
            while v8_worklist:
                cur = v8_worklist.popleft()
                for dst in self.nodes[cur].edges:
                    mark_and_push(dst)
                self.color[cur] = "BLACK"
            while cpp_worklist:
                cur = cpp_worklist.popleft()
                for dst in self.nodes[cur].edges:
                    mark_and_push(dst)
                self.color[cur] = "BLACK"

        for n in self.nodes.values():
            n.weak_edges = [w for w in n.weak_edges if self.color.get(w) == "BLACK"]

        reclaimed = [nid for nid in list(self.nodes) if self.color[nid] == "WHITE"]
        for nid in reclaimed:
            del self.nodes[nid]
        return reclaimed

    def incremental_marking_with_mutator_write(
        self, use_write_barrier: bool
    ) -> tuple[bool, list[str]]:
        """Demonstrates why missing CppHeap::WriteBarrier loses a live cross-heap object."""
        self.color = {nid: "WHITE" for nid in self.nodes}
        worklist: deque[str] = deque()
        for r in sorted(self.roots, reverse=True):
            self.color[r] = "GREY"
            worklist.append(r)

        assert worklist and worklist[0] == "v8_parent"
        parent = worklist.popleft()
        for dst in self.nodes[parent].edges:
            if self.color[dst] == "WHITE":
                self.color[dst] = "GREY"
                worklist.append(dst)
        self.color[parent] = "BLACK"

        self.nodes["v8_parent"].edges.append("cpp_payload")
        if use_write_barrier and self.color["cpp_payload"] == "WHITE":
            self.color["cpp_payload"] = "GREY"
            worklist.append("cpp_payload")
        self.nodes["cpp_holder"].edges.remove("cpp_payload")

        while worklist:
            cur = worklist.popleft()
            for dst in self.nodes[cur].edges:
                if self.color[dst] == "WHITE":
                    self.color[dst] = "GREY"
                    worklist.append(dst)
            self.color[cur] = "BLACK"

        reclaimed = [nid for nid in list(self.nodes) if self.color[nid] == "WHITE"]
        for nid in reclaimed:
            del self.nodes[nid]
        payload_survived = "cpp_payload" in self.nodes
        return payload_survived, reclaimed


def verify_model_a() -> dict[str, object]:
    iso = IsolatedMultiHeap()
    for nid, dom in [
        ("gc_live", "GC"),
        ("rc_live", "RC"),
        ("gc_dead", "GC"),
        ("rc_dead", "RC"),
        ("gc_cyc2", "GC"),
        ("rc_cyc2", "RC"),
        ("gc_cyc4_a", "GC"),
        ("gc_cyc4_b", "GC"),
        ("rc_cyc4_a", "RC"),
        ("rc_cyc4_b", "RC"),
    ]:
        iso.add_node(nid, dom)

    iso.gc_roots.add("gc_live")
    iso.add_edge("gc_live", "rc_live")
    iso.add_edge("gc_dead", "rc_dead")
    iso.add_edge("gc_cyc2", "rc_cyc2")
    iso.add_edge("rc_cyc2", "gc_cyc2")
    iso.add_edge("gc_cyc4_a", "gc_cyc4_b")
    iso.add_edge("gc_cyc4_b", "rc_cyc4_a")
    iso.add_edge("rc_cyc4_a", "rc_cyc4_b")
    iso.add_edge("rc_cyc4_b", "gc_cyc4_a")

    reclaimed_iso, rounds = iso.collect_to_fixpoint()
    assert set(reclaimed_iso) == {"gc_dead", "rc_dead"}, f"unexpected: {reclaimed_iso}"
    leaked_iso = sorted(
        (set(iso.gc_nodes) | set(iso.rc_nodes)) - {"gc_live", "rc_live"}
    )
    assert leaked_iso == [
        "gc_cyc2",
        "gc_cyc4_a",
        "gc_cyc4_b",
        "rc_cyc2",
        "rc_cyc4_a",
        "rc_cyc4_b",
    ]

    weak_iso = IsolatedMultiHeap()
    weak_iso.add_node("js_wrapper", "GC")
    weak_iso.add_node("dom_node", "RC")
    weak_iso.rc_roots.add("dom_node")
    weak_iso.add_edge("js_wrapper", "dom_node")
    weak_iso.add_edge("dom_node", "js_wrapper", weak=True)
    reclaimed_weak, _ = weak_iso.collect_to_fixpoint()
    assert reclaimed_weak == ["js_wrapper"]
    assert "dom_node" in weak_iso.rc_nodes

    uni = UnifiedCrossComponentHeap()
    for nid, dom in [
        ("gc_live", "V8"),
        ("rc_live", "CPPGC"),
        ("gc_dead", "V8"),
        ("rc_dead", "CPPGC"),
        ("gc_cyc2", "V8"),
        ("rc_cyc2", "CPPGC"),
        ("gc_cyc4_a", "V8"),
        ("gc_cyc4_b", "V8"),
        ("rc_cyc4_a", "CPPGC"),
        ("rc_cyc4_b", "CPPGC"),
        ("live_cyc_v8", "V8"),
        ("live_cyc_cpp", "CPPGC"),
    ]:
        uni.add_node(nid, dom)
    uni.roots.update({"gc_live", "live_cyc_v8"})
    uni.add_edge("gc_live", "rc_live")
    uni.add_edge("gc_dead", "rc_dead")
    uni.add_edge("gc_cyc2", "rc_cyc2")
    uni.add_edge("rc_cyc2", "gc_cyc2")
    uni.add_edge("gc_cyc4_a", "gc_cyc4_b")
    uni.add_edge("gc_cyc4_b", "rc_cyc4_a")
    uni.add_edge("rc_cyc4_a", "rc_cyc4_b")
    uni.add_edge("rc_cyc4_b", "gc_cyc4_a")
    uni.add_edge("live_cyc_v8", "live_cyc_cpp")
    uni.add_edge("live_cyc_cpp", "live_cyc_v8")

    reclaimed_uni = uni.unified_gc()
    assert set(reclaimed_uni) == {
        "gc_dead",
        "rc_dead",
        "gc_cyc2",
        "rc_cyc2",
        "gc_cyc4_a",
        "gc_cyc4_b",
        "rc_cyc4_a",
        "rc_cyc4_b",
    }
    assert set(uni.nodes) == {"gc_live", "rc_live", "live_cyc_v8", "live_cyc_cpp"}

    def build_barrier_graph() -> UnifiedCrossComponentHeap:
        g = UnifiedCrossComponentHeap()
        g.add_node("v8_parent", "V8")
        g.add_node("cpp_holder", "CPPGC")
        g.add_node("cpp_payload", "CPPGC")
        g.roots.update({"v8_parent", "cpp_holder"})
        g.add_edge("cpp_holder", "cpp_payload")
        return g

    survived_no_barrier, lost_no_barrier = build_barrier_graph().incremental_marking_with_mutator_write(
        use_write_barrier=False
    )
    survived_with_barrier, lost_with_barrier = build_barrier_graph().incremental_marking_with_mutator_write(
        use_write_barrier=True
    )
    assert not survived_no_barrier and "cpp_payload" in lost_no_barrier
    assert survived_with_barrier and lost_with_barrier == []

    return {
        "isolated_fixpoint_rounds": rounds,
        "isolated_leaked_cycle_nodes": len(leaked_iso),
        "weak_backedge_prematurely_reclaimed": reclaimed_weak,
        "unified_reclaimed_unreachable_nodes": len(reclaimed_uni),
        "unified_live_preserved": len(uni.nodes),
        "missing_write_barrier_lost_object": not survived_no_barrier,
        "with_write_barrier_preserved": survived_with_barrier,
    }


# =============================================================================
# Model B: Go cgo Transitive Pointer-Passing & Shallow runtime.Pinner Verifier
# =============================================================================

class CgoPointerViolation(RuntimeError):
    pass


class PinnerLeakPanic(RuntimeError):
    pass


@dataclass
class GoObject:
    obj_id: str
    kind: str
    fields: dict[str, str | None] = field(default_factory=dict)
    pin_count: int = 0
    in_user_arena: bool = False


class GoCgoRuntimeModel:
    """Models Go cmd/cgo pointer rules, runtime/cgocall.go checks, and runtime.Pinner."""

    def __init__(self) -> None:
        self.go_heap: dict[str, GoObject] = {}
        self.c_heap: dict[str, dict[str, str | None]] = {}
        self.go_roots: set[str] = set()

    def alloc_go(
        self,
        obj_id: str,
        kind: str = "struct",
        fields: dict[str, str | None] | None = None,
        in_user_arena: bool = False,
    ) -> str:
        self.go_heap[obj_id] = GoObject(
            obj_id=obj_id,
            kind=kind,
            fields=dict(fields or {}),
            in_user_arena=in_user_arena,
        )
        return obj_id

    def alloc_c(self, obj_id: str, slots: dict[str, str | None] | None = None) -> str:
        self.c_heap[obj_id] = dict(slots or {})
        return obj_id

    def is_go_ptr(self, ptr: str | None) -> bool:
        return ptr is not None and ptr in self.go_heap

    def is_pinned(self, ptr: str) -> bool:
        return self.go_heap[ptr].pin_count > 0

    def cgo_check_pointer(
        self,
        ptr: str,
        *,
        field_only: str | None = None,
        implicit_top: bool = True,
    ) -> None:
        if not self.is_go_ptr(ptr):
            return
        visited: set[tuple[str, bool]] = set()

        def check_obj(obj_id: str, top: bool, only_field: str | None = None) -> None:
            key = (obj_id, top)
            if key in visited:
                return
            visited.add(key)
            obj = self.go_heap[obj_id]
            if obj.kind in ("chan", "map"):
                raise CgoPointerViolation(
                    f"cgo argument {obj_id} of kind {obj.kind} always contains internal Go pointers"
                )
            if not top and not self.is_pinned(obj_id):
                raise CgoPointerViolation(
                    f"cgo argument has Go pointer to unpinned Go pointer {obj_id}"
                )
            if only_field is not None and obj.kind == "struct":
                items = [(only_field, obj.fields[only_field])]
            else:
                items = list(obj.fields.items())
            for _, target in items:
                if target is None or not self.is_go_ptr(target):
                    continue
                check_obj(target, top=False)

        check_obj(ptr, top=implicit_top, only_field=field_only)

    def c_store_go_pointer_after_call(self, c_obj_id: str, slot: str, go_ptr: str) -> None:
        self.c_heap[c_obj_id][slot] = go_ptr

    def run_go_gc(self) -> tuple[list[str], list[tuple[str, str, str]]]:
        live: set[str] = set()
        work = deque(self.go_roots | {oid for oid, o in self.go_heap.items() if o.pin_count > 0})
        while work:
            cur = work.popleft()
            if cur in live or cur not in self.go_heap:
                continue
            live.add(cur)
            for dst in self.go_heap[cur].fields.values():
                if dst in self.go_heap and dst not in live:
                    work.append(dst)
        swept = [oid for oid in list(self.go_heap) if oid not in live]
        for oid in swept:
            del self.go_heap[oid]

        uaf_dangling: list[tuple[str, str, str]] = []
        for cid, slots in self.c_heap.items():
            for slot, target in slots.items():
                if target is not None and target not in self.go_heap and target not in self.c_heap:
                    uaf_dangling.append((cid, slot, target))
        return swept, uaf_dangling


class RuntimePinner:
    """Models Go 1.21+ runtime.Pinner: strictly shallow, leak-panics if GC'd un-unpinned."""

    def __init__(self, rt: GoCgoRuntimeModel) -> None:
        self._rt = rt
        self._refs: list[str] = []

    def pin(self, ptr: str) -> None:
        if not self._rt.is_go_ptr(ptr):
            return
        obj = self._rt.go_heap[ptr]
        if obj.in_user_arena:
            raise CgoPointerViolation(f"runtime.Pinner: object {ptr} was allocated into an arena")
        obj.pin_count += 1
        self._refs.append(ptr)

    def unpin(self) -> None:
        for ptr in self._refs:
            if ptr in self._rt.go_heap:
                self._rt.go_heap[ptr].pin_count -= 1
                assert self._rt.go_heap[ptr].pin_count >= 0
        self._refs.clear()

    def simulate_gc_finalizer(self) -> None:
        if self._refs:
            self.unpin()
            raise PinnerLeakPanic(
                "runtime.Pinner: found leaking pinned pointer; forgot to call Unpin()?"
            )


def verify_model_b() -> dict[str, object]:
    rt = GoCgoRuntimeModel()
    c_buf = rt.alloc_c("c_buf")
    flat = rt.alloc_go("go_flat", "struct", {"c_ptr": c_buf})
    inner = rt.alloc_go("go_inner", "scalar")
    outer = rt.alloc_go("go_outer", "struct", {"nested": inner, "flat_c": c_buf})
    slice_backing = rt.alloc_go(
        "go_slice_backing", "slice_backing", {"[0]": None, "[1]": None, "[2]": inner}
    )
    arena_obj = rt.alloc_go("go_arena", "scalar", in_user_arena=True)
    ch = rt.alloc_go("go_chan", "chan")

    rt.cgo_check_pointer(flat)

    caught_nested = False
    try:
        rt.cgo_check_pointer(outer)
    except CgoPointerViolation:
        caught_nested = True
    assert caught_nested

    pinner = RuntimePinner(rt)
    pinner.pin(outer)
    caught_shallow = False
    try:
        rt.cgo_check_pointer(outer)
    except CgoPointerViolation:
        caught_shallow = True
    assert caught_shallow

    pinner.pin(inner)
    rt.cgo_check_pointer(outer)

    pinner.unpin()
    rt.cgo_check_pointer(outer, field_only="flat_c")

    caught_slice_backing = False
    try:
        rt.cgo_check_pointer(slice_backing, field_only="[0]")
    except CgoPointerViolation:
        caught_slice_backing = True
    assert caught_slice_backing

    caught_arena = False
    try:
        pinner.pin(arena_obj)
    except CgoPointerViolation:
        caught_arena = True
    assert caught_arena

    caught_chan = False
    try:
        rt.cgo_check_pointer(ch)
    except CgoPointerViolation:
        caught_chan = True
    assert caught_chan

    ephemeral = rt.alloc_go("go_ephemeral", "scalar")
    c_holder = rt.alloc_c("c_holder")
    rt.c_store_go_pointer_after_call(c_holder, "stashed", ephemeral)
    swept, uaf = rt.run_go_gc()
    assert "go_ephemeral" in swept
    assert uaf == [("c_holder", "stashed", "go_ephemeral")]

    leaky = RuntimePinner(rt)
    kept = rt.alloc_go("go_kept", "scalar")
    leaky.pin(kept)
    caught_leak_panic = False
    try:
        leaky.simulate_gc_finalizer()
    except PinnerLeakPanic:
        caught_leak_panic = True
    assert caught_leak_panic

    return {
        "caught_unpinned_nested_go_ptr": caught_nested,
        "caught_shallow_pin_insufficiency": caught_shallow,
        "caught_slice_backing_unpinned_elem": caught_slice_backing,
        "caught_arena_pin_rejection": caught_arena,
        "caught_c_retained_unpinned_uaf": len(uaf) == 1,
        "caught_pinner_leak_panic": caught_leak_panic,
    }


# =============================================================================
# Model C: Reentrant FFI Callback & Exclusive Aliasing (&mut / noalias)
# =============================================================================

class AliasingUB(RuntimeError):
    pass


class ReentrantBorrowDenied(RuntimeError):
    pass


class RevokedHandleTrap(RuntimeError):
    pass


class ExclusiveBorrowMemoryModel:
    """Simplified Stacked/Tree Borrows + LLVM noalias protector model."""

    def __init__(self, initial: bytes) -> None:
        self.buf = bytearray(initial)
        self.active_protector: tuple[int, str] | None = None

    def enter_mut_scope(self, tag_id: int) -> None:
        if self.active_protector is not None:
            raise AliasingUB(
                f"Overlapping &mut protector: existing={self.active_protector}, new={tag_id}"
            )
        self.active_protector = (tag_id, "mut")

    def exit_mut_scope(self, tag_id: int) -> None:
        assert self.active_protector == (tag_id, "mut")
        self.active_protector = None

    def access_raw(self, tag_id: int, write_val: int | None = None) -> int:
        if self.active_protector is not None and self.active_protector[0] != tag_id:
            raise AliasingUB(
                f"Foreign reentrant access via tag={tag_id} violated active &mut protector {self.active_protector}"
            )
        if write_val is not None:
            self.buf[0] = write_val
        return self.buf[0]


class BorrowTokenGuardedBuffer:
    """Dynamic borrow-token / Wasm may_enter style guard preventing aliasing UB."""

    def __init__(self, initial: bytes) -> None:
        self._buf = bytearray(initial)
        self._mut_borrowed = False
        self._shared_borrows = 0

    def with_mut(self, fn: Callable[[bytearray], None]) -> None:
        if self._mut_borrowed or self._shared_borrows > 0:
            raise ReentrantBorrowDenied("Cannot acquire &mut while buffer is already borrowed")
        self._mut_borrowed = True
        try:
            fn(self._buf)
        finally:
            self._mut_borrowed = False

    def with_shared(self, fn: Callable[[bytes], int]) -> int:
        if self._mut_borrowed:
            raise ReentrantBorrowDenied("Cannot acquire &T while &mut borrow is active")
        self._shared_borrows += 1
        try:
            return fn(bytes(self._buf))
        finally:
            self._shared_borrows -= 1


class GenerationalHandleTable:
    """Revocable (slot, generation) handle table (Wasm borrow<T> / scoped userdata)."""

    def __init__(self) -> None:
        self._slots: list[tuple[int, bytearray | None]] = []

    def insert_scoped(self, buf: bytearray) -> tuple[int, int]:
        slot = len(self._slots)
        gen = 1
        self._slots.append((gen, buf))
        return (slot, gen)

    def revoke(self, handle: tuple[int, int]) -> None:
        slot, gen = handle
        cur_gen, _ = self._slots[slot]
        assert cur_gen == gen
        self._slots[slot] = (cur_gen + 1, None)

    def read_byte(self, handle: tuple[int, int]) -> int:
        slot, gen = handle
        cur_gen, buf = self._slots[slot]
        if cur_gen != gen or buf is None:
            raise RevokedHandleTrap(f"Use of revoked/stale handle {handle} (current gen={cur_gen})")
        return buf[0]


def verify_model_c() -> dict[str, object]:
    mem = ExclusiveBorrowMemoryModel(b"\x2a")
    caught_ub = False
    mem.enter_mut_scope(tag_id=1)
    try:
        mem.access_raw(tag_id=2, write_val=0x99)
    except AliasingUB:
        caught_ub = True
    finally:
        mem.exit_mut_scope(tag_id=1)
    assert caught_ub

    guarded = BorrowTokenGuardedBuffer(b"\x2a")
    caught_reentrant = False

    def caller_mut_op(buf: bytearray) -> None:
        nonlocal caught_reentrant
        buf[0] = 0x2b
        try:
            guarded.with_shared(lambda view: view[0])
        except ReentrantBorrowDenied:
            caught_reentrant = True

    guarded.with_mut(caller_mut_op)
    assert caught_reentrant

    table = GenerationalHandleTable()
    stashed_handle: list[tuple[int, int]] = []
    underlying = bytearray(b"\x7f")
    h = table.insert_scoped(underlying)
    observed_in_scope = table.read_byte(h)
    stashed_handle.append(h)
    table.revoke(h)

    caught_revoked = False
    try:
        table.read_byte(stashed_handle[0])
    except RevokedHandleTrap:
        caught_revoked = True
    assert observed_in_scope == 0x7F and caught_revoked

    return {
        "unguarded_reentrant_mut_ub_detected": caught_ub,
        "borrow_token_blocked_reentrancy": caught_reentrant,
        "handle_in_scope_read_ok": observed_in_scope == 0x7F,
        "stashed_handle_trapped_after_revoke": caught_revoked,
    }


# =============================================================================
# Model D: GIL x Rust Mutex ABBA Deadlock & 3.13t Suspendable Critical Sections
# =============================================================================

def verify_model_d() -> dict[str, object]:
    def search_deadlocks(detach_before_rust_lock: bool) -> tuple[int, bool]:
        init = (0, 0, None, None)
        seen = {init}
        q = deque([init])
        deadlock_found = False

        while q:
            pc1, pc2, gil, rmx = q.popleft()
            if pc1 == 3 and pc2 == 3:
                continue
            nexts: list[tuple[int, int, str | None, str | None]] = []

            if pc1 == 0 and rmx is None:
                nexts.append((1, pc2, gil, "T1"))
            elif pc1 == 1 and gil is None:
                nexts.append((2, pc2, "T1", rmx))
            elif pc1 == 2:
                nexts.append((3, pc2, None, None))

            if not detach_before_rust_lock:
                if pc2 == 0 and gil is None:
                    nexts.append((pc1, 1, "T2", rmx))
                elif pc2 == 1 and rmx is None:
                    nexts.append((pc1, 2, gil, "T2"))
                elif pc2 == 2:
                    nexts.append((pc1, 3, None, None))
            else:
                if pc2 == 0 and gil is None:
                    nexts.append((pc1, 1, "T2", rmx))
                elif pc2 == 1:
                    if rmx is None:
                        nexts.append((pc1, 2, gil, "T2"))
                    else:
                        nexts.append((pc1, 10, None, rmx))
                elif pc2 == 10 and rmx is None:
                    nexts.append((pc1, 11, gil, "T2"))
                elif pc2 == 11 and gil is None:
                    nexts.append((pc1, 2, "T2", rmx))
                elif pc2 == 2:
                    nexts.append((pc1, 3, None, None))

            if not nexts:
                deadlock_found = True
            for st in nexts:
                if st not in seen:
                    seen.add(st)
                    q.append(st)
        return len(seen), deadlock_found

    naive_states, naive_deadlock = search_deadlocks(detach_before_rust_lock=False)
    pyo3_states, pyo3_deadlock = search_deadlocks(detach_before_rust_lock=True)
    assert naive_deadlock is True
    assert pyo3_deadlock is False

    obj_state = {"x": 0, "y": 0, "mutex_held_by": None}
    cs_stack_A: list[str] = []

    assert obj_state["mutex_held_by"] is None
    obj_state["mutex_held_by"] = "A"
    cs_stack_A.append("active")
    obj_state["x"] = 1

    obj_state["mutex_held_by"] = None
    cs_stack_A[-1] = "suspended"

    assert obj_state["mutex_held_by"] is None
    obj_state["mutex_held_by"] = "B"
    torn_observed = (obj_state["x"], obj_state["y"])
    obj_state["mutex_held_by"] = None

    obj_state["mutex_held_by"] = "A"
    cs_stack_A[-1] = "active"
    obj_state["y"] = 1
    obj_state["mutex_held_by"] = None

    assert torn_observed == (1, 0)
    return {
        "naive_interleaving_states": naive_states,
        "naive_abba_deadlock_reachable": naive_deadlock,
        "pyo3_lock_py_attached_states": pyo3_states,
        "pyo3_abba_deadlock_reachable": pyo3_deadlock,
        "cpython_313t_cs_suspend_torn_pair": list(torn_observed),
    }


# =============================================================================
# Model E: Process-Global POSIX Signal Chaining Collision Matrix
# =============================================================================

def verify_model_e() -> dict[str, object]:
    class SignalTable:
        def __init__(self, libjsig_preloaded: bool) -> None:
            self.libjsig_preloaded = libjsig_preloaded
            self.jvm_installed: set[int] = set()
            self.os_handler: dict[int, Callable[[str], str]] = {}
            self.saved_by_jsig: dict[int, Callable[[str], str]] = {}

        def install_jvm(self, sig: int, handler: Callable[[str], str]) -> None:
            prev = self.os_handler.get(sig)
            if prev is not None:
                self.saved_by_jsig[sig] = prev
            self.os_handler[sig] = handler
            self.jvm_installed.add(sig)

        def sigaction(self, sig: int, handler: Callable[[str], str]) -> None:
            if self.libjsig_preloaded and sig in self.jvm_installed:
                self.saved_by_jsig[sig] = handler
            else:
                self.os_handler[sig] = handler

        def deliver(self, sig: int, fault_origin: str) -> str:
            h = self.os_handler[sig]
            res = h(fault_origin)
            if res == "CHAIN" and sig in self.saved_by_jsig:
                return self.saved_by_jsig[sig](fault_origin)
            return res

    SIGSEGV = 11

    def jvm_handler(origin: str) -> str:
        if origin in ("jvm_implicit_null", "jvm_safepoint_poll"):
            return "JVM_HANDLED_NPE_OR_SAFEPOINT"
        return "CHAIN"

    def native_crash_handler(origin: str) -> str:
        return f"NATIVE_FATAL_CRASH({origin})"

    no_jsig = SignalTable(libjsig_preloaded=False)
    no_jsig.install_jvm(SIGSEGV, jvm_handler)
    no_jsig.sigaction(SIGSEGV, native_crash_handler)
    no_jsig_npe = no_jsig.deliver(SIGSEGV, "jvm_implicit_null")
    assert no_jsig_npe == "NATIVE_FATAL_CRASH(jvm_implicit_null)"

    with_jsig = SignalTable(libjsig_preloaded=True)
    with_jsig.install_jvm(SIGSEGV, jvm_handler)
    with_jsig.sigaction(SIGSEGV, native_crash_handler)
    jsig_npe = with_jsig.deliver(SIGSEGV, "jvm_implicit_null")
    jsig_native = with_jsig.deliver(SIGSEGV, "native_segfault")
    assert jsig_npe == "JVM_HANDLED_NPE_OR_SAFEPOINT"
    assert jsig_native == "NATIVE_FATAL_CRASH(native_segfault)"

    return {
        "without_libjsig_jvm_null_check": no_jsig_npe,
        "with_libjsig_jvm_null_check": jsig_npe,
        "with_libjsig_chained_native_fault": jsig_native,
    }


def main() -> int:
    results = {
        "model_a_cross_heap_cycles": verify_model_a(),
        "model_b_go_cgo_pinner": verify_model_b(),
        "model_c_reentrant_aliasing": verify_model_c(),
        "model_d_locks_and_cs": verify_model_d(),
        "model_e_signal_chaining": verify_model_e(),
    }
    for name, metrics in results.items():
        print(f"[PASS] {name}: {metrics}")
    print("ALL 5 MULTI-RUNTIME FFI INVARIANT MODELS VERIFIED.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
