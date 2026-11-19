#!/usr/bin/env python3
"""Standalone executable semantic verifier for non-Von-Neumann compiler models.

Verifies four executable operational models using only the Python 3.10+ stdlib:
  1. Mill-style bounded FIFO Belt + inline speculative metadata lattice
     (None > NaR(provenance) > Value) + block-argument `conform` compiler +
     speculative hoisting + prologue/epilogue-free `RETIRE` phased loops +
     vector `smear`/`smearx` early-exit masking.
  2. Graphcore-style Bulk Synchronous Parallel (BSP) phase-effect verifier
     proving schedule-permutation determinism and data-race freedom across
     strict Compute -> HardwareSync -> CompiledExchange supersteps.
  3. Tenstorrent Tensix (TT-Metalium) multi-core Circular Buffer (CB)
     protocol verifier checking exact wrap-boundary contiguity, single-producer
     single-consumer pointer ownership, cumulative wait discipline, and
     state-space deadlock freedom across BRISC/NCRISC/TRISC interleavings.
  4. Janus-style reversible bijective kernel verification (forward/inverse
     round-trip identity with zero ancilla garbage).

Exits 0 iff all positive proofs and negative fault-detection checks pass.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
import random
from typing import Any, Callable


# =============================================================================
# PART 1: Mill-Style Bounded FIFO Belt, None > NaR > Value Lattice, conform,
#         Speculative Hoisting, RETIRE Phased Loops, and Vector smear/smearx
# =============================================================================


class MillTrap(Exception):
    """Raised when a non-speculable operation consumes a NaR or faults."""

    def __init__(self, fault_kind: str, origin_pc: int, consumer: str) -> None:
        super().__init__(f"MillTrap(kind={fault_kind}, origin_pc={origin_pc}, consumer={consumer})")
        self.fault_kind = fault_kind
        self.origin_pc = origin_pc
        self.consumer = consumer


@dataclass(frozen=True)
class Val:
    """Valid scalar operand carrying element width (bytes) and per-operand FP flags."""

    value: int
    width: int = 8
    fp_flags: int = 0  # Bitmask of per-operand IEEE-754 flags (no global FCSR!)


@dataclass(frozen=True)
class NaR:
    """Not-a-Result speculative fault token preserving fault kind and origin PC."""

    fault_kind: str
    origin_pc: int
    width: int = 8


@dataclass(frozen=True)
class NoneOp:
    """Absent/masked operand with strictly higher lattice precedence than NaR."""

    width: int = 8


Operand = Val | NaR | NoneOp


def lattice_rank(op: Operand) -> int:
    """Lattice precedence: NoneOp (2) > NaR (1) > Val (0)."""
    if isinstance(op, NoneOp):
        return 2
    if isinstance(op, NaR):
        return 1
    return 0


def spec_binary(
    op_name: str,
    a: Operand,
    b: Operand,
    pc: int,
    fn: Callable[[int, int], tuple[int, int]] | Callable[[int, int], int],
    *,
    allow_zero_rhs: bool = True,
    fp_flag_fn: Callable[[int, int], int] | None = None,
) -> Operand:
    """Speculable binary ALU op respecting None > NaR(provenance) > Value."""
    # None strictly dominates both NaR and Val.
    if isinstance(a, NoneOp) or isinstance(b, NoneOp):
        w = a.width if isinstance(a, NoneOp) else b.width
        return NoneOp(width=w)
    # NaR propagates with deterministic left-to-right provenance preservation.
    if isinstance(a, NaR):
        return a
    if isinstance(b, NaR):
        return b
    # Width polymorphism with hardware width-mismatch detection.
    if a.width != b.width:
        return NaR("WIDTH_MISMATCH", pc, width=max(a.width, b.width))
    if not allow_zero_rhs and b.value == 0:
        return NaR("DIV_ZERO", pc, width=a.width)
    raw = fn(a.value, b.value)
    if isinstance(raw, tuple):
        res, extra_flags = raw
    else:
        res = raw
        extra_flags = fp_flag_fn(a.value, b.value) if fp_flag_fn else 0
    return Val(res, width=a.width, fp_flags=a.fp_flags | b.fp_flags | extra_flags)


def mill_pick(cond: Operand, t_val: Operand, f_val: Operand) -> Operand:
    """Zero-cycle conditional select at cycle boundary.

    - None condition -> None
    - NaR condition -> propagates condition NaR
    - True condition -> returns t_val (untaken f_val NaR is silently discarded)
    - False condition -> returns f_val (untaken t_val NaR is silently discarded)
    """
    if isinstance(cond, NoneOp):
        return NoneOp(width=t_val.width)
    if isinstance(cond, NaR):
        return cond
    return t_val if cond.value != 0 else f_val


def mill_spec_load(mem: dict[int, int], addr: Operand, pc: int, valid_range: range, width: int = 8) -> Operand:
    """Speculable memory load: never traps directly; produces NaR on fault or None on masked address."""
    if isinstance(addr, NoneOp):
        return NoneOp(width=width)
    if isinstance(addr, NaR):
        return addr
    if addr.value not in valid_range:
        return NaR("OOB_LOAD", pc, width=width)
    return Val(mem.get(addr.value, 0), width=width, fp_flags=0)


def mill_store(
    mem: dict[int, int],
    addr: Operand,
    data: Operand,
    pc: int,
    valid_range: range,
    committed_fp_flags: list[int] | None = None,
) -> bool:
    """Non-speculable store: strips metadata to raw payload, no-ops on None, traps on NaR.

    Returns True iff a memory write actually committed, False if suppressed by None.
    """
    # None > NaR: if EITHER address or data is None, the store is a silent no-op!
    if isinstance(addr, NoneOp) or isinstance(data, NoneOp):
        return False
    if isinstance(addr, NaR):
        raise MillTrap(addr.fault_kind, addr.origin_pc, consumer=f"store@pc{pc}:addr")
    if isinstance(data, NaR):
        raise MillTrap(data.fault_kind, data.origin_pc, consumer=f"store@pc{pc}:data")
    if addr.value not in valid_range:
        raise MillTrap("OOB_STORE", pc, consumer=f"store@pc{pc}:bounds")
    # Metadata is processor-internal and stripped on store to untagged memory.
    mem[addr.value] = data.value
    if committed_fp_flags is not None:
        committed_fp_flags[0] |= data.fp_flags
    return True


def mill_smear_inclusive(pred_vec: list[bool]) -> list[bool]:
    """Inclusive smear: sets all lanes at and after the first True to True."""
    out: list[bool] = []
    seen = False
    for p in pred_vec:
        if p:
            seen = True
        out.append(seen)
    return out


def mill_smear_exclusive(pred_vec: list[bool]) -> list[bool]:
    """Exclusive smear (smearx): sets all lanes strictly after the first True to True."""
    out: list[bool] = []
    seen = False
    for p in pred_vec:
        out.append(seen)
        if p:
            seen = True
    return out


class BeltMachine:
    """Bounded FIFO Belt with temporal de Bruijn addressing and Base/Fence scratchpad."""

    def __init__(self, belt_len: int = 8, scratchpad_slots: int = 32) -> None:
        if belt_len < 1:
            raise ValueError("belt_len must be >= 1")
        self.belt_len = belt_len
        self._belt: deque[Operand] = deque([NoneOp()] * belt_len, maxlen=belt_len)
        self.scratchpad: list[Operand] = [NoneOp()] * scratchpad_slots
        self.base = 0
        self.fence = scratchpad_slots

    def read(self, offset: int) -> Operand:
        if not (0 <= offset < self.belt_len):
            raise IndexError(f"temporal belt offset b{offset} exceeds belt_len={self.belt_len}")
        return self._belt[offset]

    def drop_cycle(self, results: list[Operand]) -> None:
        """Atomically drop a cycle's results at the front of the belt.

        By convention, results[0] lands at b0, results[1] at b1, etc., shifting
        prior entries backward by len(results) and discarding entries >= belt_len.
        """
        if len(results) > self.belt_len:
            raise ValueError("single cycle drops exceed belt_len")
        for r in reversed(results):
            self._belt.appendleft(r)

    def spill(self, belt_offset: int, sp_slot: int) -> None:
        phys = self.base + sp_slot
        if not (self.base <= phys < self.fence):
            raise MillTrap("SCRATCHPAD_FENCE", -1, consumer="spill")
        self.scratchpad[phys] = self.read(belt_offset)

    def fill(self, sp_slot: int) -> Operand:
        phys = self.base + sp_slot
        if not (self.base <= phys < self.fence):
            raise MillTrap("SCRATCHPAD_FENCE", -1, consumer="fill")
        return self.scratchpad[phys]

    def snapshot(self, k: int | None = None) -> list[Operand]:
        n = self.belt_len if k is None else k
        return list(self._belt)[:n]


@dataclass(frozen=True)
class ConformOp:
    """Atomic edge-side belt conformation instruction.

    Each source is either ('belt', offset) or ('sp', slot), read *simultaneously*
    from the predecessor state before dropping onto the front of the belt so that
    target block-argument i lands at exact temporal offset b_i.
    """

    sources: tuple[tuple[str, int], ...]


def compile_conform_edge(
    pred_belt_names: list[str | None],
    pred_sp_map: dict[str, int],
    target_block_args: list[str],
    belt_len: int,
) -> ConformOp:
    """Compile a CFG edge from a predecessor's temporal layout to a join's block-arg signature.

    Unlike Briggs/Sreedhar SSA phi destruction over mutable registers, a belt
    conformation reads all source offsets simultaneously before dropping, so cyclic
    permutations like (x, y) <-> (y, x) or 3-cycles (a, b, c) -> (b, c, a) require
    ZERO temporary registers and suffer zero lost-copy/swap hazards.
    """
    if len(target_block_args) > belt_len:
        raise ValueError("join block arguments exceed belt_len")
    # Check if prefix already matches identically (zero-cost nop edge).
    if pred_belt_names[: len(target_block_args)] == target_block_args:
        return ConformOp(sources=())
    srcs: list[tuple[str, int]] = []
    for name in target_block_args:
        if name in pred_belt_names:
            srcs.append(("belt", pred_belt_names.index(name)))
        elif name in pred_sp_map:
            srcs.append(("sp", pred_sp_map[name]))
        else:
            raise KeyError(f"SSA value {name!r} unavailable on predecessor belt or scratchpad")
    return ConformOp(sources=tuple(srcs))


def execute_conform(machine: BeltMachine, op: ConformOp) -> None:
    """Execute an atomic belt conformation drop."""
    if not op.sources:
        return
    gathered: list[Operand] = []
    for kind, idx in op.sources:
        if kind == "belt":
            gathered.append(machine.read(idx))
        elif kind == "sp":
            gathered.append(machine.fill(idx))
        else:
            raise ValueError(f"unknown source kind {kind!r}")
    machine.drop_cycle(gathered)


def verify_mill_lattice_and_conform() -> dict[str, Any]:
    """Verify lattice precedence, speculative hoisting, conform cycles, RETIRE, and smear."""
    # 1. Exhaustive lattice check: None > NaR > Val on binary ALU and store.
    v_ok = Val(10, width=8, fp_flags=0b01)
    v_ok2 = Val(2, width=8, fp_flags=0b10)
    nar_a = NaR("OOB_LOAD", origin_pc=100, width=8)
    nar_b = NaR("DIV_ZERO", origin_pc=200, width=8)
    none_v = NoneOp(width=8)

    # None beats NaR regardless of operand position.
    assert isinstance(spec_binary("add", none_v, nar_a, 1, lambda x, y: x + y), NoneOp)
    assert isinstance(spec_binary("add", nar_a, none_v, 1, lambda x, y: x + y), NoneOp)
    # NaR beats Val and preserves origin PC.
    res_nar = spec_binary("add", v_ok, nar_b, 2, lambda x, y: x + y)
    assert res_nar == nar_b
    # Per-operand FP flags accumulate without global state.
    res_val = spec_binary("add", v_ok, v_ok2, 3, lambda x, y: x + y)
    assert res_val == Val(12, width=8, fp_flags=0b11)
    # Width mismatch yields NaR.
    assert spec_binary("add", Val(1, width=4), Val(2, width=8), 4, lambda x, y: x + y) == NaR(
        "WIDTH_MISMATCH", 4, width=8
    )

    # Store suppression under None > NaR: even storing NaR to None addr (or None to NaR addr) is a no-op!
    dummy_mem: dict[int, int] = {}
    assert mill_store(dummy_mem, none_v, nar_a, 5, range(0, 16)) is False
    assert mill_store(dummy_mem, nar_a, none_v, 6, range(0, 16)) is False
    assert dummy_mem == {}

    # 2. Speculative hoisting over guarded load + divide + pick.
    mem = {0: 40, 1: 84, 2: 100}
    valid_range = range(0, 3)

    def run_hoisted_kernel(idx: int, denom: int, fallback: int, buggy_unguarded: bool = False) -> tuple[int, int]:
        m = BeltMachine(belt_len=8)
        out_mem: dict[int, int] = {}
        committed_fp = [0]
        # Cycle 0: drop inputs (idx, denom, fallback) -> b0=idx, b1=denom, b2=fallback
        m.drop_cycle([Val(idx), Val(denom), Val(fallback)])
        # Cycle 1: unconditionally hoist load(mem[idx]) (pc=10) AND evaluate cond
        loaded = mill_spec_load(mem, m.read(0), pc=10, valid_range=valid_range)
        cond_val = 1 if (buggy_unguarded or (0 <= idx < 3 and denom != 0)) else 0
        # Drop [loaded, cond] -> b0=loaded, b1=cond, b2=idx, b3=denom, b4=fallback
        m.drop_cycle([loaded, Val(cond_val)])
        # Cycle 2: unconditionally hoist div(loaded, denom) (pc=20), with synthetic INEXACT flag if remainder != 0
        div_res = spec_binary(
            "div",
            m.read(0),
            m.read(3),
            pc=20,
            fn=lambda x, y: (x // y, 0b100 if (x % y) != 0 else 0),
            allow_zero_rhs=False,
        )
        # Drop [div_res] -> b0=div_res, b1=loaded, b2=cond, b3=idx, b4=denom, b5=fallback
        m.drop_cycle([div_res])
        # Zero-cycle pick at cycle boundary: pick(cond, div_res, fallback)
        selected = mill_pick(m.read(2), m.read(0), m.read(5))
        # Non-speculable store commits result and only selected operand's FP flags.
        mill_store(out_mem, Val(0), selected, pc=30, valid_range=range(0, 1), committed_fp_flags=committed_fp)
        return out_mem[0], committed_fp[0]

    assert run_hoisted_kernel(idx=1, denom=4, fallback=-1) == (21, 0)
    assert run_hoisted_kernel(idx=1, denom=5, fallback=-1) == (16, 0b100)
    # Out-of-bounds hoisted load produces NaR@10 -> propagated through div -> discarded by pick!
    assert run_hoisted_kernel(idx=99, denom=4, fallback=-7) == (-7, 0)
    # Div-by-zero hoisted divide produces NaR@20 -> discarded by pick!
    assert run_hoisted_kernel(idx=0, denom=0, fallback=-9) == (-9, 0)
    # Negative control: buggy guard lets NaR reach store -> precise trap with origin PC!
    trapped_oob = False
    try:
        run_hoisted_kernel(idx=99, denom=4, fallback=-1, buggy_unguarded=True)
    except MillTrap as exc:
        trapped_oob = exc.fault_kind == "OOB_LOAD" and exc.origin_pc == 10
    assert trapped_oob, "Expected precise OOB_LOAD trap at origin PC 10"

    trapped_div0 = False
    try:
        run_hoisted_kernel(idx=1, denom=0, fallback=-1, buggy_unguarded=True)
    except MillTrap as exc:
        trapped_div0 = exc.fault_kind == "DIV_ZERO" and exc.origin_pc == 20
    assert trapped_div0, "Expected precise DIV_ZERO trap at origin PC 20"

    # 3. Block-argument `conform` compiler on Briggs/Sreedhar 2-swap, 3-cycle, and scratchpad spill.
    # Edge A has belt [x, y, z]; Edge B has belt [y, z, x]; Edge C spilled x to scratchpad[0] and has belt [z, y].
    # Target join block signature expects exact belt prefix [x, y, z].
    join_sig = ["x", "y", "z"]
    edge_a = compile_conform_edge(["x", "y", "z"], {}, join_sig, belt_len=6)
    edge_b = compile_conform_edge(["y", "z", "x"], {}, join_sig, belt_len=6)
    edge_c = compile_conform_edge(["z", "y", None], {"x": 0}, join_sig, belt_len=6)
    assert edge_a.sources == ()  # Already conformed -> zero instructions!
    assert edge_b.sources == (("belt", 2), ("belt", 0), ("belt", 1))
    assert edge_c.sources == (("sp", 0), ("belt", 1), ("belt", 0))

    # Execute all three predecessor edges on identical logical values (x=11, y=22, z=33).
    expected = [Val(11), Val(22), Val(33)]
    for label, init_belt, sp_init, op in [
        ("edge_a", [Val(11), Val(22), Val(33)], {}, edge_a),
        ("edge_b", [Val(22), Val(33), Val(11)], {}, edge_b),
        ("edge_c", [Val(33), Val(22)], {0: Val(11)}, edge_c),
    ]:
        bm = BeltMachine(belt_len=6)
        bm.drop_cycle(init_belt)
        for slot, val in sp_init.items():
            bm.scratchpad[slot] = val
        execute_conform(bm, op)
        assert bm.snapshot(3) == expected, f"conform failed on {label}: {bm.snapshot(3)}"

    # 4. Phased software-pipelined loop (RETIRE with None warmup, zero prologue/epilogue).
    # 3-stage pipeline:
    #   Stage 0: load a[i] (if i < n else None)
    #   Stage 1: compute y = 3 * a_prev + 1
    #   Stage 2: store b[i-2] = y_prev (suppressed automatically on None during warmup!)
    def run_phased_loop(arr: list[int]) -> list[int]:
        n = len(arr)
        a_mem = {i: v for i, v in enumerate(arr)}
        b_mem: dict[int, int] = {}
        # Pipeline stage registers initialized by RETIRE with None (zero prologue!).
        s0_val: Operand = NoneOp()
        s0_idx: Operand = NoneOp()
        s1_val: Operand = NoneOp()
        s1_idx: Operand = NoneOp()
        # Run n + 2 cycles in the single steady-state kernel body (stage latency = 2).
        for cyc in range(n + 2):
            # Stage 2 (consumes s1): store silently no-ops while s1_idx/s1_val are None!
            mill_store(b_mem, s1_idx, s1_val, pc=300, valid_range=range(0, n))
            # Stage 1 (consumes s0): speculable ALU propagates None during warmup!
            next_s1_val = spec_binary(
                "aff",
                s0_val,
                Val(3),
                pc=301,
                fn=lambda x, y: x * y + 1,
            )
            next_s1_idx = s0_idx
            # Stage 0 (issues new iteration or None on drain):
            if cyc < n:
                next_s0_val = mill_spec_load(a_mem, Val(cyc), pc=302, valid_range=range(0, n))
                next_s0_idx: Operand = Val(cyc)
            else:
                next_s0_val = NoneOp()
                next_s0_idx = NoneOp()
            s0_val, s0_idx = next_s0_val, next_s0_idx
            s1_val, s1_idx = next_s1_val, next_s1_idx
        return [b_mem[i] for i in range(n)]

    for length in (0, 1, 2, 3, 7, 16):
        inp = [i * 5 - 3 for i in range(length)]
        ref = [3 * x + 1 for x in inp]
        got = run_phased_loop(inp)
        assert got == ref, f"phased loop mismatch for length={length}: {got} != {ref}"

    # 5. Vector `smear` / `smearx` early-exit `strcpy` loop over buffer ending before vector width.
    # Valid source buffer has 6 bytes "hello\0" at addresses 0..5; vector width is 8 (lanes 6..7 are OOB!).
    src_bytes = {0: ord("h"), 1: ord("e"), 2: ord("l"), 3: ord("l"), 4: ord("o"), 5: 0}
    src_valid = range(0, 6)
    dst_mem: dict[int, int] = {}
    dst_valid = range(0, 6)
    vec_width = 8
    # Speculative vector load across lanes 0..7: lanes 6..7 yield NaR("OOB_LOAD")!
    loaded_vec = [mill_spec_load(src_bytes, Val(i), pc=400 + i, valid_range=src_valid, width=1) for i in range(vec_width)]
    assert isinstance(loaded_vec[6], NaR) and isinstance(loaded_vec[7], NaR)
    # Null check (NaR compares as False for termination predicate; lane 5 is True).
    is_nul = [isinstance(x, Val) and x.value == 0 for x in loaded_vec]
    # Exclusive smear marks lanes strictly AFTER '\0' (lanes 6..7) as terminated -> mask them to None!
    after_nul = mill_smear_exclusive(is_nul)
    assert after_nul == [False, False, False, False, False, False, True, True]
    inc_mask = mill_smear_inclusive(is_nul)
    assert inc_mask == [False, False, False, False, False, True, True, True]
    masked_vec = [mill_pick(Val(1 if drop else 0), NoneOp(width=1), elem) for drop, elem in zip(after_nul, loaded_vec)]
    # Store all 8 lanes: lanes 0..5 write "hello\0", lanes 6..7 are None (suppressing OOB store AND NaR!).
    writes = 0
    for i, elem in enumerate(masked_vec):
        if mill_store(dst_mem, Val(i), elem, pc=500 + i, valid_range=dst_valid):
            writes += 1
    assert writes == 6
    assert bytes(dst_mem[i] for i in range(6)) == b"hello\x00"

    return {
        "lattice_laws": "PASS",
        "speculative_hoisting_and_provenance": "PASS",
        "conform_cycles_and_spill": "PASS",
        "retire_phased_loop_lengths_checked": [0, 1, 2, 3, 7, 16],
        "vector_smear_oob_suppression": "PASS",
    }


# =============================================================================
# PART 2: Graphcore-Style BSP Phase-Effect Verifier & Determinism Proof
# =============================================================================


class BspPhaseViolation(Exception):
    """Static violation of BSP phase separation or contention-free exchange."""


@dataclass(frozen=True)
class ComputeOp:
    tile_id: int
    read_tile: int
    read_addr: int
    write_tile: int
    write_addr: int
    fn: Callable[[int], int]


@dataclass(frozen=True)
class ExchangeTransfer:
    src_tile: int
    src_addr: int
    dst_tile: int
    dst_addr: int


@dataclass(frozen=True)
class BspSuperstep:
    compute_ops: tuple[ComputeOp, ...]
    exchange_transfers: tuple[ExchangeTransfer, ...]


def typecheck_bsp_superstep(step: BspSuperstep, num_tiles: int) -> None:
    """Static phase-effect checker for a BSP Compute -> Sync -> Exchange superstep.

    Enforces:
      1. ComputePhase isolation: every ComputeOp on tile t accesses ONLY tile t's
         local SRAM (zero cross-tile reads/writes) and disjointly per write slot
         within a single parallel step.
      2. ExchangePhase contention-freedom: every ExchangeTransfer targets a unique
         (dst_tile, dst_addr), guaranteeing permutation determinism independent of
         packet arrival order.
    """
    compute_writes: set[tuple[int, int]] = set()
    for op in step.compute_ops:
        if not (0 <= op.tile_id < num_tiles):
            raise BspPhaseViolation(f"invalid tile_id {op.tile_id}")
        if op.read_tile != op.tile_id or op.write_tile != op.tile_id:
            raise BspPhaseViolation(
                f"ComputePhase remote access forbidden: tile {op.tile_id} accessed "
                f"read_tile={op.read_tile}, write_tile={op.write_tile}"
            )
        wkey = (op.write_tile, op.write_addr)
        if wkey in compute_writes:
            raise BspPhaseViolation(f"ComputePhase intra-tile write conflict at {wkey}")
        compute_writes.add(wkey)

    exchange_dsts: set[tuple[int, int]] = set()
    for xfer in step.exchange_transfers:
        if not (0 <= xfer.src_tile < num_tiles and 0 <= xfer.dst_tile < num_tiles):
            raise BspPhaseViolation(f"invalid exchange tile endpoint in {xfer}")
        dkey = (xfer.dst_tile, xfer.dst_addr)
        if dkey in exchange_dsts:
            raise BspPhaseViolation(f"ExchangePhase destination contention at {dkey}")
        exchange_dsts.add(dkey)


def execute_bsp_program(
    init_sram: list[dict[int, int]],
    steps: list[BspSuperstep],
    rng: random.Random | None = None,
) -> list[dict[int, int]]:
    """Execute a typechecked BSP program with optional adversarial intra-phase shuffling."""
    num_tiles = len(init_sram)
    for st in steps:
        typecheck_bsp_superstep(st, num_tiles)
    sram = [dict(tile_mem) for tile_mem in init_sram]
    for st in steps:
        # Phase 1: Local Compute (order across tiles is shuffled to test independence).
        ops = list(st.compute_ops)
        if rng is not None:
            rng.shuffle(ops)
        # Within a tile, read from pre-step SRAM snapshot and write local results.
        pre_compute = [dict(m) for m in sram]
        for op in ops:
            sram[op.write_tile][op.write_addr] = op.fn(pre_compute[op.read_tile][op.read_addr])
        # Phase 2: Hardware Global Sync (barrier).
        post_sync_snapshot = [dict(m) for m in sram]
        # Phase 3: Compiled Exchange (contention-free all-to-all transfer; shuffled arrival order).
        xfers = list(st.exchange_transfers)
        if rng is not None:
            rng.shuffle(xfers)
        for xf in xfers:
            sram[xf.dst_tile][xf.dst_addr] = post_sync_snapshot[xf.src_tile][xf.src_addr]
    return sram


def verify_bsp_phase_semantics() -> dict[str, Any]:
    """Verify BSP permutation determinism and negative violation detection."""
    num_tiles = 4
    init = [{0: (t + 1) * 10, 1: 0} for t in range(num_tiles)]
    # 3 supersteps of ring exchange + local affine update:
    # Compute: slot 1 = slot 0 + 3; Exchange: tile t sends slot 1 -> tile (t+1)%4 slot 0.
    steps = [
        BspSuperstep(
            compute_ops=tuple(
                ComputeOp(t, t, 0, t, 1, lambda x, k=s: x + 3 + k) for t in range(num_tiles)
            ),
            exchange_transfers=tuple(
                ExchangeTransfer(t, 1, (t + 1) % num_tiles, 0) for t in range(num_tiles)
            ),
        )
        for s in range(3)
    ]
    ref_out = execute_bsp_program(init, steps, rng=None)
    # Check determinism across 25 randomized intra-phase schedules.
    for seed in range(25):
        got = execute_bsp_program(init, steps, rng=random.Random(seed))
        assert got == ref_out, f"BSP nondeterminism detected on seed={seed}"

    # Negative check 1: Remote read during ComputePhase rejected statically.
    bad_compute = BspSuperstep(
        compute_ops=(ComputeOp(tile_id=0, read_tile=1, read_addr=0, write_tile=0, write_addr=1, fn=lambda x: x),),
        exchange_transfers=(),
    )
    caught_remote = False
    try:
        typecheck_bsp_superstep(bad_compute, num_tiles)
    except BspPhaseViolation:
        caught_remote = True
    assert caught_remote, "Failed to reject remote read in ComputePhase"

    # Negative check 2: Destination write collision during ExchangePhase rejected statically.
    bad_exchange = BspSuperstep(
        compute_ops=(),
        exchange_transfers=(
            ExchangeTransfer(0, 0, 2, 0),
            ExchangeTransfer(1, 0, 2, 0),
        ),
    )
    caught_collision = False
    try:
        typecheck_bsp_superstep(bad_exchange, num_tiles)
    except BspPhaseViolation:
        caught_collision = True
    assert caught_collision, "Failed to reject ExchangePhase write contention"

    return {
        "tiles": num_tiles,
        "supersteps": len(steps),
        "randomized_schedules_identical": 25,
        "remote_compute_rejected": True,
        "exchange_contention_rejected": True,
    }


# =============================================================================
# PART 3: Tenstorrent Tensix (TT-Metalium) Circular Buffer Protocol Verifier
# =============================================================================


class CbProtocolViolation(Exception):
    """Violation of TT-Metalium CB wrap-exactness, SPSC ownership, or wait protocol."""


@dataclass(frozen=True)
class CbState:
    """Faithful model of TT-Metalium dataflow_api.h / cb_api.h circular buffer state."""

    capacity: int
    rd_ptr: int = 0
    wr_ptr: int = 0
    tiles_received_u16: int = 0
    tiles_acked_u16: int = 0
    producer: str | None = None
    consumer: str | None = None

    def occupancy(self) -> int:
        return (self.tiles_received_u16 - self.tiles_acked_u16) & 0xFFFF

    def free_space(self) -> int:
        return self.capacity - self.occupancy()


@dataclass(frozen=True)
class CbAction:
    kind: str  # "reserve_back" | "push_back" | "wait_front" | "pop_front"
    cb_id: int
    n: int


def step_cb_action(
    cb: CbState,
    core_name: str,
    action: CbAction,
) -> CbState | None:
    """Attempt one CB operation; return None if blocked, new CbState if enabled, or raise on violation."""
    n = action.n
    if n < 0 or n > cb.capacity:
        raise CbProtocolViolation(f"{core_name}: {action.kind}({n}) exceeds capacity {cb.capacity}")

    if action.kind == "reserve_back":
        if cb.producer is not None and cb.producer != core_name:
            raise CbProtocolViolation(f"SPSC producer violation on cb{action.cb_id}: {cb.producer} vs {core_name}")
        if cb.free_space() < n:
            return None  # Blocked polling free space
        return CbState(
            capacity=cb.capacity,
            rd_ptr=cb.rd_ptr,
            wr_ptr=cb.wr_ptr,
            tiles_received_u16=cb.tiles_received_u16,
            tiles_acked_u16=cb.tiles_acked_u16,
            producer=core_name,
            consumer=cb.consumer,
        )

    if action.kind == "push_back":
        if cb.producer is not None and cb.producer != core_name:
            raise CbProtocolViolation(f"SPSC producer violation on cb{action.cb_id}: {cb.producer} vs {core_name}")
        # Exact TT-Metalium wrap-contiguity invariant (dataflow_api.h L217-223):
        # fifo_wr_ptr += n; ASSERT(fifo_wr_ptr <= fifo_limit); if == fifo_limit: reset to 0.
        new_wr = cb.wr_ptr + n
        if new_wr > cb.capacity:
            raise CbProtocolViolation(
                f"WrapBoundaryViolation on cb{action.cb_id}: wr_ptr={cb.wr_ptr} + push({n}) > cap={cb.capacity}"
            )
        if new_wr == cb.capacity:
            new_wr = 0
        if cb.occupancy() + n > cb.capacity:
            raise CbProtocolViolation(f"Overflow on cb{action.cb_id}: push({n}) without reserve")
        return CbState(
            capacity=cb.capacity,
            rd_ptr=cb.rd_ptr,
            wr_ptr=new_wr,
            tiles_received_u16=(cb.tiles_received_u16 + n) & 0xFFFF,
            tiles_acked_u16=cb.tiles_acked_u16,
            producer=core_name,
            consumer=cb.consumer,
        )

    if action.kind == "wait_front":
        if cb.consumer is not None and cb.consumer != core_name:
            raise CbProtocolViolation(f"SPSC consumer violation on cb{action.cb_id}: {cb.consumer} vs {core_name}")
        if cb.occupancy() < n:
            return None  # Blocked polling tiles_received - tiles_acked
        return CbState(
            capacity=cb.capacity,
            rd_ptr=cb.rd_ptr,
            wr_ptr=cb.wr_ptr,
            tiles_received_u16=cb.tiles_received_u16,
            tiles_acked_u16=cb.tiles_acked_u16,
            producer=cb.producer,
            consumer=core_name,
        )

    if action.kind == "pop_front":
        if cb.consumer is not None and cb.consumer != core_name:
            raise CbProtocolViolation(f"SPSC consumer violation on cb{action.cb_id}: {cb.consumer} vs {core_name}")
        # Exact TT-Metalium wrap-contiguity invariant (dataflow_api.h L269-275).
        new_rd = cb.rd_ptr + n
        if new_rd > cb.capacity:
            raise CbProtocolViolation(
                f"WrapBoundaryViolation on cb{action.cb_id}: rd_ptr={cb.rd_ptr} + pop({n}) > cap={cb.capacity}"
            )
        if new_rd == cb.capacity:
            new_rd = 0
        if cb.occupancy() < n:
            raise CbProtocolViolation(f"Underflow on cb{action.cb_id}: pop({n}) with occupancy={cb.occupancy()}")
        return CbState(
            capacity=cb.capacity,
            rd_ptr=new_rd,
            wr_ptr=cb.wr_ptr,
            tiles_received_u16=cb.tiles_received_u16,
            tiles_acked_u16=(cb.tiles_acked_u16 + n) & 0xFFFF,
            producer=cb.producer,
            consumer=core_name,
        )

    raise ValueError(f"unknown action kind {action.kind!r}")


def check_tensix_cb_system(
    cb_capacities: dict[int, int],
    core_programs: dict[str, tuple[CbAction, ...]],
) -> tuple[str, int, Any]:
    """Exhaustive BFS over all interleavings of Tensix cores communicating via CBs.

    Returns ("SAFE", states_explored, None) if every path terminates cleanly,
    ("DEADLOCK", states_explored, pcs_and_cbs) if any reachable non-terminal state
    has zero enabled transitions, or ("VIOLATION", states_explored, error_msg)
    on wrap-boundary / SPSC / underflow / overflow violations.
    """
    core_names = tuple(sorted(core_programs.keys()))
    cb_ids = tuple(sorted(cb_capacities.keys()))
    init_pcs = tuple(0 for _ in core_names)
    init_cbs = tuple(CbState(capacity=cb_capacities[cid]) for cid in cb_ids)
    cb_idx = {cid: i for i, cid in enumerate(cb_ids)}

    start = (init_pcs, init_cbs)
    visited = {start}
    q = deque([start])

    while q:
        pcs, cbs = q.popleft()
        all_done = all(pcs[i] == len(core_programs[core_names[i]]) for i in range(len(core_names)))
        if all_done:
            continue
        progressed = False
        for i, cname in enumerate(core_names):
            pc = pcs[i]
            prog = core_programs[cname]
            if pc >= len(prog):
                continue
            act = prog[pc]
            cbi = cb_idx[act.cb_id]
            try:
                next_cb = step_cb_action(cbs[cbi], cname, act)
            except CbProtocolViolation as exc:
                return ("VIOLATION", len(visited), str(exc))
            if next_cb is None:
                continue
            progressed = True
            next_pcs = pcs[:i] + (pc + 1,) + pcs[i + 1 :]
            next_cbs = cbs[:cbi] + (next_cb,) + cbs[cbi + 1 :]
            nxt = (next_pcs, next_cbs)
            if nxt not in visited:
                visited.add(nxt)
                q.append(nxt)
        if not progressed:
            summary = {
                cname: (pcs[i], core_programs[cname][pcs[i]] if pcs[i] < len(core_programs[cname]) else "DONE")
                for i, cname in enumerate(core_names)
            }
            return ("DEADLOCK", len(visited), summary)

    return ("SAFE", len(visited), None)


def verify_tensix_cb_protocols() -> dict[str, Any]:
    """Verify valid 3-core Tensix pipeline and catch deadlocks, wrap errors, and SPSC races."""
    # 1. Valid 3-core pipeline: NCRISC (reader) -> CB0 (cap=4) -> TRISC (compute) -> CB1 (cap=4) -> BRISC (writer)
    # 3 iterations of 2-tile batches (double-buffered, wraps cleanly at 2+2=4).
    ncrisc_ok = tuple(
        act
        for _ in range(3)
        for act in (CbAction("reserve_back", 0, 2), CbAction("push_back", 0, 2))
    )
    trisc_ok = tuple(
        act
        for _ in range(3)
        for act in (
            CbAction("wait_front", 0, 2),
            CbAction("reserve_back", 1, 2),
            CbAction("push_back", 1, 2),
            CbAction("pop_front", 0, 2),
        )
    )
    brisc_ok = tuple(
        act
        for _ in range(3)
        for act in (CbAction("wait_front", 1, 2), CbAction("pop_front", 1, 2))
    )
    status_ok, states_ok, detail_ok = check_tensix_cb_system(
        {0: 4, 1: 4},
        {"NCRISC": ncrisc_ok, "TRISC": trisc_ok, "BRISC": brisc_ok},
    )
    assert status_ok == "SAFE", f"Valid Tensix pipeline failed: {status_ok} {detail_ok}"

    # 2. Valid non-uniform cycle summing exactly to CB size (5 + 7 = 12, from cb_api.h L31-32).
    status_57, _, _ = check_tensix_cb_system(
        {0: 12},
        {
            "NCRISC": (
                CbAction("reserve_back", 0, 5),
                CbAction("push_back", 0, 5),
                CbAction("reserve_back", 0, 7),
                CbAction("push_back", 0, 7),
            ),
            "TRISC": (
                CbAction("wait_front", 0, 5),
                CbAction("pop_front", 0, 5),
                CbAction("wait_front", 0, 7),
                CbAction("pop_front", 0, 7),
            ),
        },
    )
    assert status_57 == "SAFE"

    # 3. Negative check: TT-Metalium wrap-exactness violation (7 + 7 = 14 != 12, from cb_api.h L32-33).
    status_wrap, _, detail_wrap = check_tensix_cb_system(
        {0: 12},
        {
            "NCRISC": (
                CbAction("reserve_back", 0, 7),
                CbAction("push_back", 0, 7),
                CbAction("reserve_back", 0, 7),
                CbAction("push_back", 0, 7),
            ),
            "TRISC": (
                CbAction("wait_front", 0, 7),
                CbAction("pop_front", 0, 7),
                CbAction("wait_front", 0, 7),
                CbAction("pop_front", 0, 7),
            ),
        },
    )
    assert status_wrap == "VIOLATION" and "WrapBoundaryViolation" in str(detail_wrap)

    # 4. Negative check: Circular wait deadlock between TRISC and BRISC across CB0 & CB1.
    status_dl, _, detail_dl = check_tensix_cb_system(
        {0: 2, 1: 2},
        {
            "TRISC": (CbAction("wait_front", 1, 1), CbAction("reserve_back", 0, 1), CbAction("push_back", 0, 1)),
            "BRISC": (CbAction("wait_front", 0, 1), CbAction("reserve_back", 1, 1), CbAction("push_back", 1, 1)),
        },
    )
    assert status_dl == "DEADLOCK"

    # 5. Negative check: SPSC multi-consumer violation (both TRISC and BRISC pop CB0, cb_api.h L63-65).
    status_spsc, _, detail_spsc = check_tensix_cb_system(
        {0: 4},
        {
            "NCRISC": (CbAction("reserve_back", 0, 2), CbAction("push_back", 0, 2)),
            "TRISC": (CbAction("wait_front", 0, 1), CbAction("pop_front", 0, 1)),
            "BRISC": (CbAction("wait_front", 0, 1), CbAction("pop_front", 0, 1)),
        },
    )
    assert status_spsc == "VIOLATION" and "SPSC consumer violation" in str(detail_spsc)

    # 6. Negative check: Non-cumulative repeated cb_wait_front(8) without pop returns prematurely.
    # Pushing only 8 tiles satisfies wait_front(8) twice, proving why cb_api.h L24-27 requires (8, 16).
    cb_demo = CbState(capacity=16)
    cb_demo = step_cb_action(cb_demo, "NCRISC", CbAction("reserve_back", 0, 8))
    assert cb_demo is not None
    cb_demo = step_cb_action(cb_demo, "NCRISC", CbAction("push_back", 0, 8))
    assert cb_demo is not None
    # Two repeated wait_front(8) calls both succeed even though only 8 tiles exist (not 16!):
    w1 = step_cb_action(cb_demo, "TRISC", CbAction("wait_front", 0, 8))
    w2 = step_cb_action(w1, "TRISC", CbAction("wait_front", 0, 8))  # type: ignore[arg-type]
    assert w1 is not None and w2 is not None
    # Whereas the cumulative wait_front(16) properly blocks until 16 tiles arrive:
    assert step_cb_action(w1, "TRISC", CbAction("wait_front", 0, 16)) is None  # type: ignore[arg-type]

    return {
        "valid_3core_pipeline_states_explored": states_ok,
        "valid_nonuniform_5_plus_7_wrap": "PASS",
        "wrap_7_plus_7_violation_caught": True,
        "circular_cb_deadlock_caught": True,
        "spsc_dual_pop_violation_caught": True,
        "cumulative_wait_semantics_verified": True,
    }


# =============================================================================
# PART 4: Janus-Style Reversible Bijective Kernel Verification
# =============================================================================


def janus_fib_forward(n: int, x1: int = 1, x2: int = 1) -> tuple[int, int, int]:
    """Janus reversible Fibonacci pair update (Yokoyama & Gluck 2007/2008).

    Forward loop: `from i = 0 do x1 += x2; x1 <=> x2; i += 1 until i = n`.
    Uses strictly bijective updates (+=, swap) and zero garbage tape.
    """
    if n < 0:
        raise ValueError("n must be >= 0")
    i = 0
    assert i == 0  # entry assertion
    while True:
        if i == n:
            break
        x1 += x2
        x1, x2 = x2, x1
        i += 1
        assert i != 0
    return (n, x1, x2)


def janus_fib_inverse(n: int, x1: int, x2: int) -> tuple[int, int, int]:
    """Syntactic local inversion of janus_fib_forward (zero history tape)."""
    i = n
    assert i == n  # inverted exit assertion becomes entry assertion
    while True:
        if i == 0:
            break
        i -= 1
        x1, x2 = x2, x1
        x1 -= x2
        assert i != n
    return (n, x1, x2)


def verify_reversible_bijection() -> dict[str, Any]:
    """Verify exact forward/inverse bijection with zero garbage across n=0..15."""
    for n in range(16):
        fwd = janus_fib_forward(n, 1, 1)
        inv = janus_fib_inverse(*fwd)
        assert inv == (n, 1, 1), f"Reversible round-trip failed for n={n}: {inv}"
    return {"janus_fib_bijection_n_0_to_15": "PASS"}


def main() -> int:
    results = {
        "mill_belt_nar_conform_retire_smear": verify_mill_lattice_and_conform(),
        "graphcore_bsp_phase_verifier": verify_bsp_phase_semantics(),
        "tenstorrent_tensix_cb_verifier": verify_tensix_cb_protocols(),
        "janus_reversible_bijection": verify_reversible_bijection(),
    }
    print("ALL VERIFICATION CHECKS PASSED:")
    for section, data in results.items():
        print(f"  - {section}: {data}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
