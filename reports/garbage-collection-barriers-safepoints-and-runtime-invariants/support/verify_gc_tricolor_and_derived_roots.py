#!/usr/bin/env python3
"""Executable model checker for compiler-GC runtime invariants.

Self-contained Python 3.10+ (stdlib-only) verification probe demonstrating:
1. Concurrent tri-color marking with un-rescanned stacks (no barriers on stack
   writes, concurrent stack scanning):
   - Concrete witness counterexamples AND bounded exhaustive BFS reachability
     showing that:
       * No barrier loses reachable white objects.
       * Pure Dijkstra insertion barrier (shade(new)) without stack rescan loses
         a white object moved from a grey heap object onto an already-scanned
         (black) stack.
       * Pure Yuasa SATB deletion barrier (shade(old)) without STW stack
         snapshot loses a white object moved from an unscanned (grey) stack
         into a black heap object.
       * Go's hybrid barrier (shade(old); if stack_grey: shade(new)) AND its
         unconditional implementation (shade(old); shade(new)) preserve marking
         completeness across ALL explored interleavings (0 lost-object states).
       * Pure Yuasa SATB *with* STW initial stack snapshot (as in G1 / OCaml 5)
         also preserves marking completeness across ALL explored interleavings.
2. x86-TSO store-buffer Dekker litmus check for conditional-on-black write
   barriers vs. unconditional barriers (Go runtime/mbarrier.go:68-93).
3. Moving-GC derived interior and exterior pointers across safepoints:
   - Compiler liveness dropping the base pointer (`base + offset`) causes
     use-after-relocation or mis-attributed interior/exterior pointers when
     the collector relocates the allocation.
   - Pinning `(base, derived)` relocation pairs (Diwan-Moss-Hudson 1992 /
     LLVM `gc.statepoint` + `gc.relocate`) reconstructs both interior and
     exterior derived pointers identically after compaction.
4. Generational ZGC 16-bit low-order colored-pointer shift-based load barrier
   (`RRRRMMmmFFrr0000` layout from OpenJDK `zAddress.hpp` / `zBarrier.hpp`) and
   monotonic self-healing metadata transitions.
5. Perceus / Lean 4 `reset`/`reuse` in-place reuse semantics:
   - Exact allocation-address identity and zero heap allocation when `rc == 1`
     (exclusive ownership), plus safe fresh-allocation fallback with preserved
     immutable aliasing when `rc > 1`, plus Lean 4 sticky-overflow saturation
     safety (never prematurely freeing on 32-bit RC saturation).

Exits 0 iff every expected soundness property passes and every expected buggy
configuration produces a verified counterexample.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
import sys
from typing import Iterable


# =============================================================================
# 1. Concurrent Tri-Color Marking Model Checker (Wilson / Dijkstra / Yuasa / Go)
# =============================================================================

WHITE = 0
GREY = 1
BLACK = 2
COLOR_NAMES = {WHITE: "WHITE", GREY: "GREY", BLACK: "BLACK"}

# Fixed 3-object heap (0=A, 1=B, 2=C), each with 1 pointer field,
# plus 2 goroutine stacks (S0, S1), each with 2 local registers.
OBJ_NAMES = ("A", "B", "C")


def _reachable_from_stacks(
    stacks: tuple[tuple[int | None, ...], ...],
    heap_fields: tuple[int | None, ...],
) -> set[int]:
    seen: set[int] = set()
    work: list[int] = []
    for st in stacks:
        for ref in st:
            if ref is not None and ref not in seen:
                seen.add(ref)
                work.append(ref)
    while work:
        cur = work.pop()
        nxt = heap_fields[cur]
        if nxt is not None and nxt not in seen:
            seen.add(nxt)
            work.append(nxt)
    return seen


def _shade(colors: list[int], obj: int | None) -> None:
    if obj is not None and colors[obj] == WHITE:
        colors[obj] = GREY


def explore_tricolor(
    barrier_mode: str,
    stw_stack_snapshot: bool = False,
) -> tuple[int, tuple | None, list[str]]:
    """Bounded exhaustive BFS over concurrent mutator + collector interleavings.

    State tuple:
      (stacks, stack_scanned, heap_fields, colors)
    where:
      - stacks: ((s0_r0, s0_r1), (s1_r0, s1_r1)) with entries in {None, 0, 1, 2}
      - stack_scanned: (bool, bool) — False=grey/unscanned, True=black/scanned
      - heap_fields: (fA, fB, fC) with entries in {None, 0, 1, 2}
      - colors: (cA, cB, cC) with entries in {WHITE, GREY, BLACK}

    Initial configuration at GC mark-phase start:
      - S0 holds (A, None); S1 holds (B, C) or (None, C) depending on scenario.
      We explore from a rich union of canonical initial heap/stack topologies
      representing both heap-rooted and stack-rooted white objects:
        * Init 1: S0=(A, None), S1=(B, None), heap=(A->None, B->C, C->None)
        * Init 2: S0=(A, None), S1=(C, None), heap=(A->None, B->None, C->None)
      Every object starts WHITE; if stw_stack_snapshot=True, all stacks are
      atomically scanned at mark start (all stack referents shaded GREY and
      stack_scanned=(True, True)).
    """
    init_configs = [
        # Config 1: C is only reachable via heap edge B -> C; S0 holds A, S1 holds B
        (((0, None), (1, None)), (None, 2, None)),
        # Config 2: C is only reachable from unscanned stack S1; both S0 and S1 hold A
        (((0, None), (0, 2)), (None, None, None)),
    ]

    visited: set[tuple] = set()
    queue: deque[tuple[tuple, list[str]]] = deque()

    for stacks, heap_fields in init_configs:
        colors_l = [WHITE, WHITE, WHITE]
        if stw_stack_snapshot:
            for st in stacks:
                for ref in st:
                    _shade(colors_l, ref)
            scanned = (True, True)
            desc = f"INIT(STW-snapshot): stacks={stacks}, heap={heap_fields}"
        else:
            scanned = (False, False)
            desc = f"INIT(concurrent-stacks): stacks={stacks}, heap={heap_fields}"
        st0 = (stacks, scanned, heap_fields, tuple(colors_l))
        if st0 not in visited:
            visited.add(st0)
            queue.append((st0, [desc]))

    while queue:
        state, trace = queue.popleft()
        stacks, scanned, heap_fields, colors = state

        # Termination check: all stacks scanned and no GREY objects remain.
        # Note: stacks are NEVER rescanned in this model.
        if all(scanned) and all(c != GREY for c in colors):
            live = _reachable_from_stacks(stacks, heap_fields)
            lost = sorted(o for o in live if colors[o] == WHITE)
            if lost:
                lost_names = [OBJ_NAMES[o] for o in lost]
                return (
                    len(visited),
                    state,
                    trace + [f"MARK-TERMINATE VIOLATION: reachable WHITE objects lost = {lost_names}"],
                )
            continue

        next_steps: list[tuple[tuple, str]] = []

        # --- Collector transitions ---
        # C1: Scan an unscanned stack s (shades all pointers on s, marks s BLACK)
        for si in range(2):
            if not scanned[si]:
                c_new = list(colors)
                for ref in stacks[si]:
                    _shade(c_new, ref)
                sc_new = list(scanned)
                sc_new[si] = True
                next_steps.append(
                    (
                        (stacks, tuple(sc_new), heap_fields, tuple(c_new)),
                        f"GC.scan_stack(S{si}) -> colors={[COLOR_NAMES[c] for c in c_new]}",
                    )
                )

        # C2: Blacken a GREY heap object u
        for u in range(3):
            if colors[u] == GREY:
                c_new = list(colors)
                _shade(c_new, heap_fields[u])
                c_new[u] = BLACK
                next_steps.append(
                    (
                        (stacks, scanned, heap_fields, tuple(c_new)),
                        f"GC.blacken({OBJ_NAMES[u]}) -> colors={[COLOR_NAMES[c] for c in c_new]}",
                    )
                )

        # --- Mutator transitions (stacks have NO write barriers) ---
        for si in range(2):
            st = stacks[si]
            # M1: Load heap field into a stack register: S[si][dst] = heap[src].field
            for src_r in range(2):
                obj = st[src_r]
                if obj is None:
                    continue
                loaded = heap_fields[obj]
                for dst_r in range(2):
                    if st[dst_r] == loaded:
                        continue
                    new_st = list(st)
                    new_st[dst_r] = loaded
                    new_stacks = list(stacks)
                    new_stacks[si] = tuple(new_st)
                    next_steps.append(
                        (
                            (tuple(new_stacks), scanned, heap_fields, colors),
                            f"MUT(S{si}).load: r{dst_r} = {OBJ_NAMES[obj]}.f "
                            f"({OBJ_NAMES[loaded] if loaded is not None else 'None'})",
                        )
                    )

            # M2: Clear a stack register (no write barrier on stack writes!)
            for dst_r in range(2):
                if st[dst_r] is not None:
                    new_st = list(st)
                    old_r = st[dst_r]
                    new_st[dst_r] = None
                    new_stacks = list(stacks)
                    new_stacks[si] = tuple(new_st)
                    next_steps.append(
                        (
                            (tuple(new_stacks), scanned, heap_fields, colors),
                            f"MUT(S{si}).clear_stack: r{dst_r} = None (was {OBJ_NAMES[old_r]})",
                        )
                    )

            # M3: Store to a heap object field reachable directly from stack S[si]:
            #     heap[dst_obj].field = new_val (from stack reg or None)
            #     Applies the configured write barrier.
            for dst_r in range(2):
                dst_obj = st[dst_r]
                if dst_obj is None:
                    continue
                old_val = heap_fields[dst_obj]
                candidates: list[int | None] = [None] + [r for r in st if r is not None]
                for new_val in candidates:
                    if new_val == old_val:
                        continue
                    c_new = list(colors)
                    if barrier_mode == "none":
                        pass
                    elif barrier_mode == "dijkstra":
                        # Pure insertion barrier: shade(new_val)
                        _shade(c_new, new_val)
                    elif barrier_mode == "yuasa":
                        # Pure SATB deletion barrier: shade(old_val)
                        _shade(c_new, old_val)
                    elif barrier_mode == "go_hybrid_conditional":
                        # Go Proposal 17503 conceptual hybrid barrier:
                        # shade(*slot); if current stack is grey: shade(ptr)
                        _shade(c_new, old_val)
                        if not scanned[si]:
                            _shade(c_new, new_val)
                    elif barrier_mode == "go_hybrid_unconditional":
                        # Go concrete assembly barrier: shade(*slot); shade(ptr)
                        _shade(c_new, old_val)
                        _shade(c_new, new_val)
                    else:
                        raise ValueError(f"unknown barrier mode: {barrier_mode}")

                    hf_new = list(heap_fields)
                    hf_new[dst_obj] = new_val
                    next_steps.append(
                        (
                            (stacks, scanned, tuple(hf_new), tuple(c_new)),
                            f"MUT(S{si}).store[{barrier_mode}]: "
                            f"{OBJ_NAMES[dst_obj]}.f = {OBJ_NAMES[new_val] if new_val is not None else 'None'} "
                            f"(old={OBJ_NAMES[old_val] if old_val is not None else 'None'})",
                        )
                    )

        for nxt, desc in next_steps:
            if nxt not in visited:
                visited.add(nxt)
                queue.append((nxt, trace + [desc]))

    return len(visited), None, []


def verify_tricolor_barriers() -> dict[str, object]:
    results: dict[str, object] = {}

    # Expected UNSAFE configurations without STW stack snapshot / stack rescan
    for mode in ("none", "dijkstra", "yuasa"):
        states, bad_state, trace = explore_tricolor(mode, stw_stack_snapshot=False)
        assert bad_state is not None, f"Expected lost-object counterexample for {mode} without rescan!"
        results[f"{mode}_no_rescan"] = {
            "states_visited": states,
            "sound": False,
            "counterexample_steps": len(trace),
            "trace": trace,
        }

    # Expected SOUND configurations:
    # 1. Go hybrid barrier (conditional on grey stack) — NO stack rescan, NO STW stack snapshot
    # 2. Go hybrid barrier (unconditional shade(old)+shade(new)) — NO stack rescan
    # 3. Pure Yuasa SATB WITH STW initial stack snapshot (G1 / OCaml 5)
    for key, mode, stw in [
        ("go_hybrid_conditional_no_rescan", "go_hybrid_conditional", False),
        ("go_hybrid_unconditional_no_rescan", "go_hybrid_unconditional", False),
        ("yuasa_with_stw_stack_snapshot", "yuasa", True),
    ]:
        states, bad_state, trace = explore_tricolor(mode, stw_stack_snapshot=stw)
        assert bad_state is None, f"Unexpected counterexample for {key}: {trace}"
        results[key] = {
            "states_visited": states,
            "sound": True,
            "states_exhaustively_verified": states,
        }

    return results


# =============================================================================
# 2. x86-TSO Dekker Litmus Check for Conditional-on-Black Write Barriers
# =============================================================================

def verify_tso_conditional_barrier_race() -> dict[str, object]:
    """Simulate Go mbarrier.go:68-93 store-buffer race on x86-TSO.

    Mutator (conditional Dijkstra barrier checking object color AFTER store):
        st [slot], ptr
        ld r1, [slotmark]    # if r1 == 0 (not black), skip shading ptr!
    GC worker (blackening object):
        st [slotmark], 1
        ld r2, [slot]        # if r2 == 0 (nil), GC misses ptr!

    Under SC, (r1 == 0 and r2 == 0) is impossible.
    Under x86-TSO (per-core FIFO store buffer without MFENCE), BOTH threads can
    buffer their store and read the stale 0 from main memory -> r1==0, r2==0 ->
    ptr is NEVER shaded and NEVER scanned -> LOST OBJECT!
    Inserting MFENCE on both sides (or making the write barrier unconditional)
    eliminates the lost-object outcome.
    """

    def simulate_tso(use_mfence: bool) -> set[tuple[int, int]]:
        # State: (m_pc, g_pc, mem_slot, mem_mark, m_buf, g_buf, r1, r2)
        # m_buf / g_buf: tuple of (addr, val) pending stores
        init = (0, 0, 0, 0, (), (), -1, -1)
        seen = {init}
        q = deque([init])
        outcomes: set[tuple[int, int]] = set()

        def read_mem(addr: str, mem_slot: int, mem_mark: int, buf: tuple) -> int:
            # Store-buffer forwarding: read latest buffered write to addr, else main memory
            for a, v in reversed(buf):
                if a == addr:
                    return v
            return mem_slot if addr == "slot" else mem_mark

        while q:
            m_pc, g_pc, ms, mm, mb, gb, r1, r2 = q.popleft()
            if m_pc == 2 and g_pc == 2 and not mb and not gb:
                outcomes.add((r1, r2))
                continue

            nxt_states = []
            # Flush mutator store buffer
            if mb:
                a, v = mb[0]
                nms = v if a == "slot" else ms
                nmm = v if a == "mark" else mm
                nxt_states.append((m_pc, g_pc, nms, nmm, mb[1:], gb, r1, r2))
            # Flush GC store buffer
            if gb:
                a, v = gb[0]
                nms = v if a == "slot" else ms
                nmm = v if a == "mark" else mm
                nxt_states.append((m_pc, g_pc, nms, nmm, mb, gb[1:], r1, r2))

            # Mutator step
            if m_pc == 0:
                # st [slot], 1
                nxt_states.append((1, g_pc, ms, mm, mb + (("slot", 1),), gb, r1, r2))
            elif m_pc == 1:
                # MFENCE requires empty store buffer before load
                if not use_mfence or not mb:
                    val = read_mem("mark", ms, mm, mb)
                    nxt_states.append((2, g_pc, ms, mm, mb, gb, val, r2))

            # GC step
            if g_pc == 0:
                # st [mark], 1
                nxt_states.append((m_pc, 1, ms, mm, mb, gb + (("mark", 1),), r1, r2))
            elif g_pc == 1:
                if not use_mfence or not gb:
                    val = read_mem("slot", ms, mm, gb)
                    nxt_states.append((m_pc, 2, ms, mm, mb, gb, r1, val))

            for st in nxt_states:
                if st not in seen:
                    seen.add(st)
                    q.append(st)
        return outcomes

    no_fence_outcomes = simulate_tso(use_mfence=False)
    mfence_outcomes = simulate_tso(use_mfence=True)

    assert (0, 0) in no_fence_outcomes, "Expected TSO Dekker (r1=0, r2=0) lost-object race without MFENCE!"
    assert (0, 0) not in mfence_outcomes, "MFENCE must forbid (r1=0, r2=0) on x86-TSO!"
    return {
        "tso_without_mfence_outcomes": sorted(no_fence_outcomes),
        "tso_with_mfence_outcomes": sorted(mfence_outcomes),
        "lost_object_possible_without_mfence": (0, 0) in no_fence_outcomes,
        "lost_object_possible_with_mfence": (0, 0) in mfence_outcomes,
    }


# =============================================================================
# 3. Derived Interior & Exterior Pointer Relocation Across Moving-GC Safepoints
# =============================================================================

@dataclass
class HeapObject:
    obj_id: str
    addr: int
    size: int
    payload: list[int]  # 8-byte words


class MovingHeap:
    """Two-space copying heap demonstrating relocation hazards for derived pointers."""

    def __init__(self, from_base: int = 0x1000, to_base: int = 0x8000) -> None:
        self.from_base = from_base
        self.to_base = to_base
        self.next_from = from_base
        self.next_to = to_base
        self.objects: dict[str, HeapObject] = {}
        self.live_ranges: dict[tuple[int, int], str] = {}
        self.forwarding: dict[int, int] = {}

    def alloc(self, obj_id: str, words: list[int]) -> int:
        addr = self.next_from
        size = len(words) * 8
        obj = HeapObject(obj_id, addr, size, list(words))
        self.objects[obj_id] = obj
        self.live_ranges[(addr, addr + size)] = obj_id
        self.next_from += size
        return addr

    def find_base_by_address(self, ptr: int) -> HeapObject | None:
        for (lo, hi), oid in self.live_ranges.items():
            if lo <= ptr < hi:
                return self.objects[oid]
        return None

    def read_word(self, ptr: int) -> tuple[str, int] | None:
        """Read 8-byte word at `ptr` if it lands in a currently live object; else None (dangling)."""
        obj = self.find_base_by_address(ptr)
        if obj is None or (ptr - obj.addr) % 8 != 0:
            return None
        idx = (ptr - obj.addr) // 8
        return (obj.obj_id, obj.payload[idx])

    def copy_live_objects(self, root_bases: Iterable[int]) -> dict[int, int]:
        """Relocate all reachable base addresses to to-space and poison from-space."""
        old_ranges = dict(self.live_ranges)
        self.live_ranges.clear()
        self.forwarding.clear()
        relocated_ids: set[str] = set()

        for base_addr in root_bases:
            # Find object whose base is exactly base_addr
            matched = None
            for (lo, _hi), oid in old_ranges.items():
                if lo == base_addr:
                    matched = self.objects[oid]
                    break
            if matched is None or matched.obj_id in relocated_ids:
                continue
            new_addr = self.next_to
            self.next_to += matched.size
            self.forwarding[matched.addr] = new_addr
            matched.addr = new_addr
            self.live_ranges[(new_addr, new_addr + matched.size)] = matched.obj_id
            relocated_ids.add(matched.obj_id)

        # Uncopied objects are reclaimed (from-space unmapped/reused)
        return dict(self.forwarding)


def verify_derived_pointer_relocation() -> dict[str, object]:
    """Compare three compiler strategies across a moving-GC safepoint:
      (1) Naive liveness drops `base`, keeping only `derived_interior = base + 16`:
          moving GC fails to recognize `derived_interior` as a root base ->
          object reclaimed/dangling OR address not updated -> UAF / stale read!
      (2) Naive address-lookup heuristic on an *exterior* derived pointer
          `derived_ext = arrA_base + 32` (created by loop-strength reduction /
          negative-indexed bias `p = base - 8` or `p = base + size` landing in
          adjacent allocation `arrB`): runtime address lookup mis-attributes
          `derived_ext` to `arrB` instead of `arrA`!
      (3) Statepoint `(base, derived)` relocation pair (Diwan-Moss-Hudson 1992 /
          LLVM `gc.statepoint` + `gc.relocate(tok, base_idx, derived_idx)`):
          pins `base` live across the safepoint, computes `offset = derived - base`
          before relocation, and reconstructs `derived' = base' + offset` after
          relocation — sound for BOTH interior and exterior derived pointers.
    """
    # --- Case A: Naive liveness drops base of interior derived pointer ---
    heap_a = MovingHeap()
    arr_a = heap_a.alloc("arrA", [10, 20, 30, 40])  # 32 bytes at 0x1000..0x1020
    derived_interior = arr_a + 16  # points to element 2 (value 30)
    # Naive compiler notices `arr_a` has no uses after GEP -> drops `arr_a` from root set.
    # Collector expects base roots; derived_interior is not a base -> arrA is NOT evacuated!
    heap_a.copy_live_objects(root_bases=[])
    naive_interior_read = heap_a.read_word(derived_interior)
    assert naive_interior_read is None, "Expected dangling read when base dropped!"

    # --- Case B: Exterior derived pointer lands inside adjacent object arrB ---
    heap_b = MovingHeap()
    b_arr_a = heap_b.alloc("arrA", [100, 200])  # 0x1000..0x1010 (16 bytes)
    b_arr_b = heap_b.alloc("arrB", [999, 888])  # 0x1010..0x1020 (16 bytes)
    # Loop strength reduction computes exterior pointer `p = arrA + 16` (1-past-end,
    # to be dereferenced later as `*(p - 8)` -> arrA[1] == 200).
    derived_exterior = b_arr_a + 16
    # Address-range lookup sees derived_exterior == 0x1010 inside arrB!
    misattributed = heap_b.find_base_by_address(derived_exterior)
    assert misattributed is not None and misattributed.obj_id == "arrB", (
        "Expected exterior pointer to collide with adjacent object arrB!"
    )
    # Relocate arrB first and arrA second (changing relative spacing!)
    fwd_b = heap_b.copy_live_objects(root_bases=[b_arr_b, b_arr_a])
    # If runtime relocated derived_exterior using misattributed base arrB:
    bad_relocated_ext = fwd_b[b_arr_b] + (derived_exterior - b_arr_b)
    # Dereferencing *(bad_relocated_ext - 8) reads before arrB (dangling or wrong object)!
    bad_ext_read = heap_b.read_word(bad_relocated_ext - 8)
    assert bad_ext_read is None or bad_ext_read != ("arrA", 200), (
        "Expected mis-relocated exterior pointer to corrupt access!"
    )

    # --- Case C: LLVM Statepoint / DMH-92 `(base, derived)` relocation pair ---
    heap_c = MovingHeap()
    c_arr_a = heap_c.alloc("arrA", [100, 200])
    c_arr_b = heap_c.alloc("arrB", [999, 888])
    c_interior = c_arr_a + 8   # points to 200
    c_exterior = c_arr_a + 16  # 1-past-end, collides with c_arr_b's start!

    # Statepoint stackmap records explicit (base, derived) pairs:
    statepoint_pairs = [
        ("interior", c_arr_a, c_interior),
        ("exterior", c_arr_a, c_exterior),
        ("other", c_arr_b, c_arr_b),
    ]
    # Pre-safepoint: record signed byte offsets relative to explicit base
    offsets = [(name, base, derived - base) for name, base, derived in statepoint_pairs]
    # Relocate in reversed order so arrA and arrB move to arbitrary non-adjacent slots
    fwd_c = heap_c.copy_live_objects(root_bases=[c_arr_b, c_arr_a])
    # Post-safepoint `gc.relocate`: new_derived = fwd[base] + offset
    relocated = {name: fwd_c[base] + off for name, base, off in offsets}

    assert heap_c.read_word(relocated["interior"]) == ("arrA", 200)
    assert heap_c.read_word(relocated["exterior"] - 8) == ("arrA", 200)
    assert heap_c.read_word(relocated["other"]) == ("arrB", 999)

    return {
        "naive_dropped_base_dangling": naive_interior_read is None,
        "exterior_ptr_misattributed_to": misattributed.obj_id,
        "exterior_ptr_corrupted_without_base_pair": bad_ext_read != ("arrA", 200),
        "statepoint_interior_reconstructed": heap_c.read_word(relocated["interior"]),
        "statepoint_exterior_reconstructed": heap_c.read_word(relocated["exterior"] - 8),
    }


# =============================================================================
# 4. Generational ZGC Colored-Pointer Shift Load Barrier & Monotonic Self-Heal
# =============================================================================

def verify_zgc_colored_pointer_barrier() -> dict[str, object]:
    """Model OpenJDK Generational ZGC `zAddress.hpp` / `zBarrier.hpp` layout.

    Layout of 16 low-order metadata bits in a 64-bit `zpointer`:
        bits [15:12] = RRRR (Remapped[00, 01, 10, 11], one-hot good bit)
        bits [11:10] = MM   (MarkedOld[0, 1])
        bits [ 9: 8] = mm   (MarkedYoung[0, 1])
        bits [ 7: 6] = FF   (Finalizable[0, 1])
        bits [ 5: 4] = rr   (Remembered[0, 1])
        bits [ 3: 0] = 0000 (Reserved)

    On x86-64, address bits start immediately above the single active Remapped
    good bit (overlapping high zero remap bits with low zero address bits),
    allowing one speculative right-shift by `shift = 12 + 1 + phase_idx`:
      - If raw zpointer == 0: result == 0 -> ZF=1 -> fast path (null)
      - If active remap bit == 1: last shifted-out bit sets CF=1 -> fast path
        and shifted value is the uncolored `zaddress`!
      - Otherwise (CF==0 and ZF==0 -> x86 `ja` taken): bad pointer -> slow path
        relocates/remaps and monotonically CAS self-heals the heap slot.
    """
    REMAPPED_SHIFT = 12

    def encode_zpointer(uncolored_addr: int, phase_idx: int, mark_rem_bits: int = 0) -> int:
        assert uncolored_addr % 8 == 0, "oop must be 8-byte aligned"
        assert 0 <= phase_idx <= 3
        remap_bit = 1 << (REMAPPED_SHIFT + phase_idx)
        # x86-64 overlapping layout: address starts immediately above remap_bit
        addr_shift = REMAPPED_SHIFT + 1 + phase_idx
        return (uncolored_addr << addr_shift) | remap_bit | (mark_rem_bits & 0x0FF0)

    def x86_speculative_load_barrier(zptr: int, current_phase: int) -> tuple[bool, int]:
        """Simulate single x86 `shr zptr, current_shift` + `ja slow_path`."""
        shift = REMAPPED_SHIFT + 1 + current_phase
        # Last bit shifted out becomes Carry Flag (CF)
        cf = (zptr >> (shift - 1)) & 1
        uncolored = zptr >> shift
        zf = 1 if uncolored == 0 else 0
        # x86 `ja` (jump if above) branches iff CF == 0 and ZF == 0
        slow_path_taken = (cf == 0) and (zf == 0)
        return (not slow_path_taken), uncolored

    obj_addr = 0x0000_0400_0001_2340  # 8-byte aligned heap address
    # Phase 0..3 fast-path verification and cross-phase trap verification
    for cur_phase in range(4):
        # Null always takes fast path (ZF=1)
        ok_null, addr_null = x86_speculative_load_barrier(0, cur_phase)
        assert ok_null and addr_null == 0

        # Good pointer for current phase takes fast path and yields exact uncolored addr
        good_zptr = encode_zpointer(obj_addr, cur_phase, mark_rem_bits=0x0550)
        ok_good, uncolored = x86_speculative_load_barrier(good_zptr, cur_phase)
        assert ok_good and uncolored == obj_addr, (
            f"Fast path failed for phase {cur_phase}: ok={ok_good}, got={hex(uncolored)}"
        )

        # Stale pointer from ANY other phase MUST trap to slow path (CF=0, ZF=0)!
        for stale_phase in range(4):
            if stale_phase == cur_phase:
                continue
            stale_zptr = encode_zpointer(obj_addr, stale_phase, mark_rem_bits=0x0550)
            ok_stale, _ = x86_speculative_load_barrier(stale_zptr, cur_phase)
            assert not ok_stale, (
                f"Stale phase {stale_phase} pointer escaped load barrier in phase {cur_phase}!"
            )

    # Monotonic self-healing CAS simulation:
    # Slot starts stale (phase 0) pointing to old_addr; object relocated to new_addr in phase 1.
    heap_slot = encode_zpointer(obj_addr, phase_idx=0)
    new_addr = 0x0000_0400_0009_8760
    ok_before, _ = x86_speculative_load_barrier(heap_slot, current_phase=1)
    assert not ok_before
    # Slow path remaps via forwarding table and CAS-heals heap_slot to phase 1 good color
    healed = encode_zpointer(new_addr, phase_idx=1)
    heap_slot = healed  # atomic cmpxchg succeeds
    ok_after, resolved = x86_speculative_load_barrier(heap_slot, current_phase=1)
    assert ok_after and resolved == new_addr

    return {
        "phases_checked": 4,
        "all_stale_phases_trapped": True,
        "self_healed_addr": hex(resolved),
    }


# =============================================================================
# 5. Perceus / Lean 4 `reset`/`reuse` In-Place Reuse & Sticky RC Saturation
# =============================================================================

@dataclass
class RCNode:
    addr: int
    tag: str
    head: int
    tail: RCNode | None
    rc: int = 1


class RCHeap:
    def __init__(self) -> None:
        self.next_addr = 0x2000
        self.alloc_count = 0
        self.reuse_count = 0
        self.live: dict[int, RCNode] = {}

    def alloc_cons(self, head: int, tail: RCNode | None) -> RCNode:
        addr = self.next_addr
        self.next_addr += 24
        self.alloc_count += 1
        node = RCNode(addr=addr, tag="Cons", head=head, tail=tail, rc=1)
        self.live[addr] = node
        return node

    def dup(self, node: RCNode | None) -> RCNode | None:
        if node is not None:
            node.rc += 1
        return node

    def drop(self, node: RCNode | None) -> None:
        while node is not None:
            assert node.rc > 0, "Double free detected!"
            node.rc -= 1
            if node.rc == 0:
                nxt = node.tail
                del self.live[node.addr]
                node = nxt
            else:
                break

    def reset(self, node: RCNode) -> tuple[RCNode | None, int, RCNode | None]:
        """Perceus/Lean `reset`: if rc == 1, return reuse token (node) after
        preserving child ownership; if rc > 1, decrement rc, dup children,
        and return NULL reuse token."""
        if node.rc == 1:
            # Exclusive owner: children keep their existing 1 reference from `node`
            # (no inc/dec needed on children — Lean ExpandResetReuse optimization!)
            return node, node.head, node.tail
        else:
            # Shared owner: caller must NOT mutate `node` in place.
            # Increment children before decrementing `node`.
            h = node.head
            t = self.dup(node.tail)
            self.drop(node)
            return None, h, t

    def reuse_cons(self, token: RCNode | None, head: int, tail: RCNode | None) -> RCNode:
        """Perceus/Lean `reuse`: overwrite cell in place if token != None, else alloc."""
        if token is not None:
            self.reuse_count += 1
            token.head = head
            token.tail = tail
            token.rc = 1
            return token
        return self.alloc_cons(head, tail)


def map_inc_fbip(heap: RCHeap, xs: RCNode | None) -> RCNode | None:
    """Functional-But-In-Place (FBIP) list map `(x -> x + 1)` with Perceus reset/reuse."""
    if xs is None:
        return None
    token, h, t = heap.reset(xs)
    new_t = map_inc_fbip(heap, t)
    return heap.reuse_cons(token, h + 1, new_t)


def to_py_list(xs: RCNode | None) -> list[int]:
    out: list[int] = []
    cur = xs
    while cur is not None:
        out.append(cur.head)
        cur = cur.tail
    return out


def list_addrs(xs: RCNode | None) -> list[int]:
    out: list[int] = []
    cur = xs
    while cur is not None:
        out.append(cur.addr)
        cur = cur.tail
    return out


def verify_perceus_reset_reuse_and_lean_sticky_rc() -> dict[str, object]:
    heap = RCHeap()
    # Build uniquely owned list [1, 2, 3]
    n3 = heap.alloc_cons(3, None)
    n2 = heap.alloc_cons(2, n3)
    n1 = heap.alloc_cons(1, n2)
    orig_addrs = list_addrs(n1)
    allocs_before_unique = heap.alloc_count

    # Case 1: Unique owner (rc == 1) -> 100% in-place reuse, 0 allocations, identical addresses
    mapped_unique = map_inc_fbip(heap, n1)
    assert to_py_list(mapped_unique) == [2, 3, 4]
    assert list_addrs(mapped_unique) == orig_addrs, "Expected identical cell addresses on rc==1!"
    assert heap.alloc_count == allocs_before_unique, "Expected zero fresh allocations on rc==1!"
    assert heap.reuse_count == 3

    # Case 2: Shared owner (rc == 2 at head, rc == 1 at tail) ->
    # head MUST copy (new address) preserving original [2, 3, 4]; tail nodes are still unique?
    # Note: dup(mapped_unique) only bumps root rc to 2; reset on root sees rc==2, so it dups
    # root.tail (bumping n2.rc to 2) and drops root (leaving root.rc==1). Thus ALL 3 nodes
    # along the shared spine safely copy without mutating the shared alias!
    alias = heap.dup(mapped_unique)
    allocs_before_shared = heap.alloc_count
    mapped_shared = map_inc_fbip(heap, mapped_unique)
    assert to_py_list(alias) == [2, 3, 4], "Shared immutable list was corrupted!"
    assert to_py_list(mapped_shared) == [3, 4, 5]
    assert set(list_addrs(alias)).isdisjoint(set(list_addrs(mapped_shared))), (
        "Shared copy must allocate disjoint cells!"
    )
    assert heap.alloc_count - allocs_before_shared == 3

    # Drop both lists -> zero live heap objects (garbage-free!)
    heap.drop(alias)
    heap.drop(mapped_shared)
    assert len(heap.live) == 0, f"Memory leak: {len(heap.live)} live nodes remaining!"

    # Case 3: Lean 4 signed 32-bit sticky-RC overflow model (lean.h:670-760)
    INT32_MIN = -(1 << 31)
    LEAN_RC_STICKY = INT32_MIN + 0x10000000
    LEAN_RC_STICKY_DROP = INT32_MIN + 0x20000000
    LEAN_RC_INC_MAX = 0x10000

    def to_i32(x: int) -> int:
        x &= 0xFFFFFFFF
        return x - 0x100000000 if x & 0x80000000 else x

    def to_u32(x: int) -> int:
        return x & 0xFFFFFFFF

    def lean_inc_st(rc: int, n: int) -> int:
        assert 0 < n <= LEAN_RC_INC_MAX
        if rc > 0:
            # Unsigned wrap lands in [INT32_MIN, INT32_MIN + LEAN_RC_INC_MAX) -> sticky!
            return to_i32(to_u32(rc) + n)
        if to_u32(rc) > to_u32(LEAN_RC_STICKY):
            return to_i32(rc - n)
        return rc  # Stuck/frozen: never freed

    def lean_dec_model(rc: int) -> int | None:
        if rc > 1:
            return rc - 1
        if rc == 1:
            return None  # Freed
        if rc == 0:
            return 0  # Persistent: never freed
        # MT or sticky
        if to_u32(rc) <= to_u32(LEAN_RC_STICKY_DROP):
            return rc  # Stuck/frozen: drop stops adjusting, never freed
        if rc == -1:
            return None  # MT last reference freed
        return rc + 1

    # Overflowing ST max (0x7FFFFFFF) by 1 wraps to INT32_MIN, which is <= LEAN_RC_STICKY_DROP
    # as unsigned, so subsequent drops NEVER prematurely free the object.
    rc_overflowed = lean_inc_st(0x7FFFFFFF, 1)
    assert rc_overflowed == INT32_MIN
    assert to_u32(rc_overflowed) <= to_u32(LEAN_RC_STICKY_DROP)
    for _ in range(100):
        rc_after = lean_dec_model(rc_overflowed)
        assert rc_after == rc_overflowed, "Overflowed sticky RC must never decrement or free!"

    return {
        "unique_in_place_reuses": 3,
        "unique_fresh_allocs": 0,
        "shared_fresh_allocs": 3,
        "live_objects_after_drop": len(heap.live),
        "lean_sticky_overflow_safe": True,
    }


def main() -> int:
    tri = verify_tricolor_barriers()
    tso = verify_tso_conditional_barrier_race()
    drv = verify_derived_pointer_relocation()
    zgc = verify_zgc_colored_pointer_barrier()
    rc = verify_perceus_reset_reuse_and_lean_sticky_rc()

    print("=== 1. Concurrent Tri-Color Marking Model Check ===")
    for k, v in tri.items():
        if v["sound"]:
            print(f"  [PASS/SOUND]  {k}: {v['states_exhaustively_verified']} states explored, 0 lost-object states")
        else:
            print(f"  [PASS/BUGGY]  {k}: counterexample found in {v['counterexample_steps']} steps ({v['states_visited']} states)")
            for step in v["trace"]:
                print(f"      {step}")

    print("\n=== 2. x86-TSO Conditional-on-Black Write Barrier Race ===")
    print(f"  Without MFENCE outcomes (r1, r2): {tso['tso_without_mfence_outcomes']}  (lost-object (0,0) reachable: {tso['lost_object_possible_without_mfence']})")
    print(f"  With MFENCE outcomes    (r1, r2): {tso['tso_with_mfence_outcomes']}  (lost-object (0,0) reachable: {tso['lost_object_possible_with_mfence']})")

    print("\n=== 3. Derived Interior & Exterior Pointer Relocation ===")
    print(f"  Naive dropped base -> dangling: {drv['naive_dropped_base_dangling']}")
    print(f"  Exterior ptr misattributed by address lookup to: {drv['exterior_ptr_misattributed_to']}")
    print(f"  Statepoint (base, derived) interior read: {drv['statepoint_interior_reconstructed']}")
    print(f"  Statepoint (base, derived) exterior read: {drv['statepoint_exterior_reconstructed']}")

    print("\n=== 4. Generational ZGC Shift-Based Colored-Pointer Load Barrier ===")
    print(f"  Phases checked: {zgc['phases_checked']}, all stale phases trapped: {zgc['all_stale_phases_trapped']}, self-healed: {zgc['self_healed_addr']}")

    print("\n=== 5. Perceus / Lean 4 Reset-Reuse & Sticky RC Overflow ===")
    print(f"  rc==1 in-place reuses={rc['unique_in_place_reuses']}, fresh allocs={rc['unique_fresh_allocs']}")
    print(f"  rc>1  copy fallback fresh allocs={rc['shared_fresh_allocs']}, live after drop={rc['live_objects_after_drop']}")
    print(f"  Lean 4 32-bit sticky-RC overflow safe (never prematurely freed): {rc['lean_sticky_overflow_safe']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
