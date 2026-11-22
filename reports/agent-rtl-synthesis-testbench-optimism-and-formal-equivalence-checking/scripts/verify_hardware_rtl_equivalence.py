#!/usr/bin/env python3
"""Deterministic verification suite for hardware RTL simulation blind spots,
formal equivalence checking semantics, and synthesis PPA reward proxies.

Executes with Python 3.10+ standard library only (`python3 -I -B`) in < 2.0s
with deterministic stdout across PYTHONHASHSEED settings.

Pinned upstream reference commits modeled in repository ports:
- hkust-zhiyao/RTLLM @ 51ed553d0ffd32797a1a0a13e051656bf302c81f
- NVlabs/verilog-eval @ c498220d0a52248f8e3fdffe279075215bde2da6 (v2)
- NVlabs/verilog-eval @ 4fa0ac4ed70ff1685114c25cd2e4c17cbba6a0c4 (v1)
- YosysHQ/yosys @ 11d972c2011064339498e292ad22e4a74f557f34
- YosysHQ/sby @ b21f778333efc1e7c33fe22b56d43f87e4f759d4
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
import itertools
import math
import random
import re
from typing import Callable

STATES_4: tuple[str, ...] = ("0", "1", "X", "Z")


# ============================================================================
# Pillar 1: IEEE 1364-2005 / IEEE 1800-2023 4-State Semantics & Harness Ports
# ============================================================================


def coerce_xz(bit: str) -> str:
    """IEEE 1364-2005 Sec. 5.1.10 / IEEE 1800-2023 Sec. 11.4.9:
    bitwise and arithmetic operators coerce Z bits to X."""
    return "X" if bit in ("X", "Z") else bit


def bit_not4(a: str) -> str:
    a = coerce_xz(a)
    if a == "0":
        return "1"
    if a == "1":
        return "0"
    return "X"


def bit_and4(a: str, b: str) -> str:
    a, b = coerce_xz(a), coerce_xz(b)
    if a == "0" or b == "0":
        return "0"
    if a == "1" and b == "1":
        return "1"
    return "X"


def bit_or4(a: str, b: str) -> str:
    a, b = coerce_xz(a), coerce_xz(b)
    if a == "1" or b == "1":
        return "1"
    if a == "0" and b == "0":
        return "0"
    return "X"


def bit_xor4(a: str, b: str) -> str:
    a, b = coerce_xz(a), coerce_xz(b)
    if a == "X" or b == "X":
        return "X"
    return "1" if a != b else "0"


class Vec4:
    """MSB-first multi-bit IEEE 1364/1800 4-state vector over {'0','1','X','Z'}."""

    __slots__ = ("bits",)

    def __init__(self, bits: str) -> None:
        assert len(bits) >= 1 and all(c in STATES_4 for c in bits)
        self.bits = bits

    @classmethod
    def from_int(cls, val: int, width: int) -> Vec4:
        mask = (1 << width) - 1
        return cls(format(val & mask, f"0{width}b"))

    @property
    def width(self) -> int:
        return len(self.bits)

    def is_known(self) -> bool:
        return all(b in ("0", "1") for b in self.bits)

    def to_uint(self) -> int | None:
        if not self.is_known():
            return None
        return int(self.bits, 2)

    def collapse_2state(self) -> Vec4:
        """IEEE 1800-2023 Sec. 6.11.2 2-state coercion (bit/int / Verilator): X,Z -> 0."""
        return Vec4("".join("1" if b == "1" else "0" for b in self.bits))

    def __repr__(self) -> str:
        return f"{self.width}'b{self.bits}"


def _pad_pair(a: Vec4, b: Vec4) -> tuple[str, str]:
    w = max(a.width, b.width)
    return a.bits.rjust(w, "0"), b.bits.rjust(w, "0")


def vlog_reduce_truth(v: Vec4) -> str:
    """IEEE 1800-2023 Sec. 11.4.7 truth value of an expression:
    '1' if any bit is '1'; '0' if all bits are '0'; else 'X'."""
    if "1" in v.bits:
        return "1"
    if all(b == "0" for b in v.bits):
        return "0"
    return "X"


def vlog_log_not(v: Vec4) -> Vec4:
    return Vec4(bit_not4(vlog_reduce_truth(v)))


def vlog_log_and(a: Vec4, b: Vec4) -> Vec4:
    return Vec4(bit_and4(vlog_reduce_truth(a), vlog_reduce_truth(b)))


def vlog_log_or(a: Vec4, b: Vec4) -> Vec4:
    return Vec4(bit_or4(vlog_reduce_truth(a), vlog_reduce_truth(b)))


def vlog_eq2(a: Vec4, b: Vec4) -> Vec4:
    """IEEE 1364-2005 Sec. 5.1.8 / IEEE 1800-2023 Sec. 11.4.5 logical equality (==):
    '0' if any bit position definitely differs (0 vs 1);
    'X' if any bit is X or Z and no position definitely differs;
    '1' otherwise."""
    ab, bb = _pad_pair(a, b)
    has_unknown = False
    for x, y in zip(ab, bb):
        if x in ("0", "1") and y in ("0", "1"):
            if x != y:
                return Vec4("0")
        else:
            has_unknown = True
    return Vec4("X" if has_unknown else "1")


def vlog_neq2(a: Vec4, b: Vec4) -> Vec4:
    return Vec4(bit_not4(vlog_eq2(a, b).bits))


def vlog_case_eq(a: Vec4, b: Vec4) -> Vec4:
    """IEEE 1364-2005 Sec. 5.1.8 / IEEE 1800-2023 Sec. 11.4.5 case equality (===)."""
    ab, bb = _pad_pair(a, b)
    return Vec4("1" if ab == bb else "0")


def vlog_case_neq(a: Vec4, b: Vec4) -> Vec4:
    return Vec4("0" if vlog_case_eq(a, b).bits == "1" else "1")


def vlog_bit_xor(a: Vec4, b: Vec4) -> Vec4:
    ab, bb = _pad_pair(a, b)
    return Vec4("".join(bit_xor4(x, y) for x, y in zip(ab, bb)))


def vlog_if(cond: Vec4) -> bool:
    """IEEE 1364-2005 Sec. 9.4 / IEEE 1800-2023 Sec. 12.4:
    if (cond) executes the then-branch iff truth(cond) == '1'.
    Crucially, '0', 'X', and 'Z' ALL take the else-branch (False)."""
    return vlog_reduce_truth(cond) == "1"


def vlog_ternary(cond: Vec4, if_true: Vec4, if_false: Vec4) -> Vec4:
    """IEEE 1364-2005 Sec. 5.1.13 / IEEE 1800-2023 Sec. 11.4.11 conditional (cond ? a : b):
    when cond reduces to 'X', bit i is a[i] if a[i] == b[i] in {'0','1'}, else 'X'."""
    t = vlog_reduce_truth(cond)
    tb, fb = _pad_pair(if_true, if_false)
    if t == "1":
        return Vec4(tb)
    if t == "0":
        return Vec4(fb)
    merged = "".join(
        x if (x == y and x in ("0", "1")) else "X" for x, y in zip(tb, fb)
    )
    return Vec4(merged)


def vlog_add_int(a: Vec4, b: Vec4) -> Vec4:
    """IEEE 1364-2005 Sec. 5.1.5: any X/Z bit makes the entire addition result X."""
    w = max(a.width, b.width)
    ua, ub = a.to_uint(), b.to_uint()
    if ua is None or ub is None:
        return Vec4("X" * w)
    return Vec4.from_int(ua + ub, w)


def rtllm_cal_atk_port(
    dic_list: dict[str, dict[str, int]], n: int, k: int
) -> tuple[float, float]:
    """Faithful port of hkust-zhiyao/RTLLM@51ed553d auto_run.py:28-44."""
    sum_list: list[float] = []
    for design in dic_list.keys():
        c = dic_list[design]["syntax_success"]
        sum_list.append(1.0 - math.comb(n - c, k) / math.comb(n, k))
    sum_list.append(0)  # auto_run.py:34 off-by-one denominator bug
    syntax_passk = sum(sum_list) / len(sum_list)

    sum_list = []
    for design in dic_list.keys():
        c = dic_list[design]["func_success"]
        sum_list.append(1.0 - math.comb(n - c, k) / math.comb(n, k))
    sum_list.append(0)  # auto_run.py:42 off-by-one denominator bug
    func_passk = sum(sum_list) / len(sum_list)
    return syntax_passk, func_passk


def rtllm_scrape_pass_port(output: str) -> bool:
    """Faithful port of hkust-zhiyao/RTLLM@51ed553d auto_run.py:99."""
    return ("Pass" in output) or ("pass" in output)


def rtllm_comparator_3bit_tb_port(
    dut: Callable[[int, int], tuple[Vec4, Vec4, Vec4]],
    use_case_ineq: bool = False,
) -> tuple[Vec4, bool]:
    """Faithful port of RTLLM@51ed553d Arithmetic/Comparator/comparator_3bit/testbench.v:24-45."""
    rng = random.Random(1364)
    error = Vec4.from_int(0, 32)
    one32 = Vec4.from_int(1, 32)
    zero32 = Vec4.from_int(0, 32)
    for _ in range(100):
        a = rng.randint(0, 7)
        b = rng.randint(0, 7)
        ag, ae, al = dut(a, b)
        if not use_case_ineq:
            # Exact testbench.v:33:
            # if ((A > B && !A_greater) || (A == B && !A_equal) || (A < B && !A_less))
            c1 = vlog_log_and(Vec4("1" if a > b else "0"), vlog_log_not(ag))
            c2 = vlog_log_and(Vec4("1" if a == b else "0"), vlog_log_not(ae))
            c3 = vlog_log_and(Vec4("1" if a < b else "0"), vlog_log_not(al))
            bad = vlog_log_or(vlog_log_or(c1, c2), c3)
            if vlog_if(bad):
                error = vlog_add_int(error, one32)
        else:
            exp_g = Vec4("1" if a > b else "0")
            exp_e = Vec4("1" if a == b else "0")
            exp_l = Vec4("1" if a < b else "0")
            mismatch = (
                vlog_if(vlog_case_neq(ag, exp_g))
                or vlog_if(vlog_case_neq(ae, exp_e))
                or vlog_if(vlog_case_neq(al, exp_l))
            )
            if mismatch:
                error = vlog_add_int(error, one32)
    passed = vlog_if(vlog_eq2(error, zero32))
    return error, passed


def rtllm_sequence_detector_tb_port(seq_det_trace: tuple[Vec4, Vec4, Vec4]) -> bool:
    """Faithful port of RTLLM@51ed553d Control/Finite State Machine/sequence_detector/testbench.v:33-45."""
    error = Vec4.from_int(0, 32)
    one32 = Vec4.from_int(1, 32)
    s0, s1, s2 = seq_det_trace
    if vlog_if(vlog_log_not(s0)):  # line 33: if (!sequence_detected)
        error = vlog_add_int(error, one32)
    if vlog_if(s1):  # line 37: if (sequence_detected)
        error = vlog_add_int(error, one32)
    if vlog_if(vlog_log_not(s2)):  # line 42: if (!sequence_detected)
        error = vlog_add_int(error, one32)
    return vlog_if(vlog_eq2(error, Vec4.from_int(0, 32)))


def rtllm_square_wave_tb_port(wave_samples: list[Vec4]) -> bool:
    """Faithful port of RTLLM@51ed553d Miscellaneous/Signal generation/square_wave/testbench.v:20-34."""
    ones_count = 0
    error = 0
    one1 = Vec4("1")
    for w in wave_samples:
        if vlog_if(vlog_eq2(w, one1)):
            ones_count += 1
            if ones_count > 8:
                error = 1
        else:
            ones_count = 0
    return error == 0


def verilog_eval_v1_grade_port(out: str, err: str = "") -> str:
    """Faithful port of NVlabs/verilog-eval@4fa0ac4e verilog_eval/execution.py:99-111."""
    match = re.search(r"Mismatches: ([0-9]*) in ([0-9]*) samples", out)
    if "syntax error" in err:
        return "failed: syntax error."
    if len(err) > 0:
        return "failed: compile error."
    if match:
        cor, tot = [int(i) for i in match.groups()]
        if cor == 0:  # execution.py:106 omits `and tot > 0`
            return "passed"
        return f"failed: {cor} out of {tot} samples."
    return "failed: info string not matched."


def verilog_eval_v2_grade_port(compile_log: str) -> tuple[str, int]:
    """Subset port of NVlabs/verilog-eval@c498220d scripts/sv-iv-analyze:231-322.
    Models 5 of the 12 failure codes ('S', 'T', 'p', 'C', 'R') plus '.' (pass),
    omitting specialized diagnostic codes ('e', '0', 'n', 'w', 'm', 'c', 'r')."""
    passfail = "?"
    error_c = False
    error_p = False
    no_mismatch = False
    rec_mismatch = 0
    mismatch_pattern = r"^Mismatches: (\d+) in \d+ samples$"

    for line in compile_log.splitlines():
        if "syntax error" in line:
            passfail = "S"
            break
        if "error" in line:
            error_c = True
        if "Unable to bind wire/reg" in line:
            error_p = True
        if "TIMEOUT" in line:
            passfail = "T"
            break
        match = re.match(mismatch_pattern, line)
        if match:
            num_mismatch = int(match.group(1))
            if num_mismatch == 0:
                no_mismatch = True  # sv-iv-analyze:288 sticky True, never reset!
            else:
                rec_mismatch = num_mismatch

    if passfail == "?" and error_p:
        passfail = "p"
    if passfail == "?" and error_c:
        passfail = "C"
    if passfail == "?" and no_mismatch:
        passfail = "."
    if passfail == "?":
        passfail = "R"
    return passfail, rec_mismatch


def run_probe_1() -> None:
    print("========================================================================")
    print("PROBE 1: IEEE 1364/1800 4-State Semantics & RTLLM / VerilogEval Harnesses")
    print("Provenance: [normative IEEE 1364-2005 / 1800-2023 4-state model + pinned harness subset port]")

    # 1. Exhaustive 16-pair (ref, dut) truth table for VerilogEval Prob001_zero_test.sv:98
    #    assign tb_match = ( { ref } === ( { ref } ^ { dut } ^ { ref } ) );
    ve_table: dict[tuple[str, str], str] = {}
    for r_bit, d_bit in itertools.product(STATES_4, STATES_4):
        rv, dv = Vec4(r_bit), Vec4(d_bit)
        rhs = vlog_bit_xor(vlog_bit_xor(rv, dv), rv)
        ve_table[(r_bit, d_bit)] = vlog_case_eq(rv, rhs).bits

    # Verify X-detection on defined ref, plus the two Z-state anomalies
    assert ve_table[("0", "X")] == "0" and ve_table[("1", "X")] == "0"
    assert ve_table[("0", "Z")] == "0" and ve_table[("1", "Z")] == "0"
    assert ve_table[("X", "0")] == "1" and ve_table[("X", "1")] == "1"
    assert ve_table[("X", "Z")] == "1"  # Undriven Z silently accepted when ref == X
    assert ve_table[("Z", "Z")] == "0"  # Tri-state Z === (Z ^ Z ^ Z) self-mismatch!

    # Verify IEEE 1364/1800 if (X != expected) and if (!Z) X-optimism
    assert vlog_neq2(Vec4("X"), Vec4("1")).bits == "X"
    assert vlog_neq2(Vec4("Z"), Vec4("0")).bits == "X"
    assert vlog_if(vlog_neq2(Vec4("X"), Vec4("1"))) is False
    assert vlog_if(vlog_log_not(Vec4("Z"))) is False

    # 2. RTLLM comparator_3bit, sequence_detector, and square_wave ports
    _, gold_pass = rtllm_comparator_3bit_tb_port(
        lambda a, b: (
            Vec4("1" if a > b else "0"),
            Vec4("1" if a == b else "0"),
            Vec4("1" if a < b else "0"),
        )
    )
    err_empty_z, empty_z_pass = rtllm_comparator_3bit_tb_port(
        lambda _a, _b: (Vec4("Z"), Vec4("Z"), Vec4("Z"))
    )
    err_empty_x, empty_x_pass = rtllm_comparator_3bit_tb_port(
        lambda _a, _b: (Vec4("X"), Vec4("X"), Vec4("X"))
    )
    err_all_ones, all_ones_pass = rtllm_comparator_3bit_tb_port(
        lambda _a, _b: (Vec4("1"), Vec4("1"), Vec4("1"))
    )
    err_fixed_z, fixed_z_pass = rtllm_comparator_3bit_tb_port(
        lambda _a, _b: (Vec4("Z"), Vec4("Z"), Vec4("Z")),
        use_case_ineq=True,
    )
    err_fixed_ones, fixed_ones_pass = rtllm_comparator_3bit_tb_port(
        lambda _a, _b: (Vec4("1"), Vec4("1"), Vec4("1")),
        use_case_ineq=True,
    )
    assert gold_pass is True
    assert empty_z_pass is True and err_empty_z.to_uint() == 0
    assert empty_x_pass is True and err_empty_x.to_uint() == 0
    assert all_ones_pass is True and err_all_ones.to_uint() == 0
    assert fixed_z_pass is False and err_fixed_z.to_uint() == 100
    assert fixed_ones_pass is False and err_fixed_ones.to_uint() == 100

    seq_empty_z_pass = rtllm_sequence_detector_tb_port((Vec4("Z"), Vec4("Z"), Vec4("Z")))
    sq_empty_z_pass = rtllm_square_wave_tb_port([Vec4("Z")] * 200)
    sq_const0_pass = rtllm_square_wave_tb_port([Vec4("0")] * 200)
    assert seq_empty_z_pass is True
    assert sq_empty_z_pass is True and sq_const0_pass is True

    # 3. 4-state `integer error` ternary bit-tainting vs 2-state Verilator / `int` X-collapse
    err_4state = Vec4.from_int(0, 32)
    cond_4s = vlog_eq2(Vec4("Z" * 8), Vec4.from_int(0, 8))  # 'X'
    err_4state = vlog_ternary(
        cond_4s, err_4state, vlog_add_int(err_4state, Vec4.from_int(1, 32))
    )
    ternary_4state_passes = vlog_if(vlog_eq2(err_4state, Vec4.from_int(0, 32)))
    assert err_4state.bits == ("0" * 31 + "X") and ternary_4state_passes is False

    dut_2state = Vec4("Z" * 8).collapse_2state()
    err_2state = Vec4.from_int(0, 32)
    cond_2s = vlog_eq2(dut_2state, Vec4.from_int(0, 8))  # '1' when ref == 0!
    err_2state = vlog_ternary(
        cond_2s, err_2state, vlog_add_int(err_2state, Vec4.from_int(1, 32))
    )
    ternary_2state_passes = vlog_if(vlog_eq2(err_2state, Vec4.from_int(0, 32)))
    assert ternary_2state_passes is True

    # 4. RTLLM auto_run.py cal_atk N+1 denominator deflation & substring pass scrape
    perfect_50 = {f"d{i}": {"syntax_success": 5, "func_success": 5} for i in range(50)}
    syn_atk, func_atk = rtllm_cal_atk_port(perfect_50, n=5, k=1)
    assert abs(syn_atk - 50.0 / 51.0) < 1e-12 and abs(func_atk - 50.0 / 51.0) < 1e-12
    assert rtllm_scrape_pass_port("debug: pass_request=0, failed=100\n") is True

    # 5. VerilogEval v1 & v2 $finish-at-t=0 zero-sample bypass and sticky no_mismatch
    zero_sample_log = "Simulation finished at 0 ps\nMismatches: 0 in 0 samples\n"
    sticky_log = (
        "Mismatches: 0 in 1 samples\n"
        "Simulation finished at 205 ps\n"
        "Mismatches: 20 in 20 samples\n"
    )
    assert verilog_eval_v1_grade_port(zero_sample_log) == "passed"
    v2_zero_code, _ = verilog_eval_v2_grade_port(zero_sample_log)
    v2_sticky_code, v2_sticky_mm = verilog_eval_v2_grade_port(sticky_log)
    assert v2_zero_code == "."
    assert v2_sticky_code == "." and v2_sticky_mm == 20

    print(
        f"  VerilogEval XOR-idiom truth table: (X,Z)->{ve_table[('X', 'Z')]} (accepts Z on don't-care), "
        f"(Z,Z)->{ve_table[('Z', 'Z')]} (tri-state self-mismatch)"
    )
    print(
        f"  RTLLM comparator_3bit: empty_Z_pass={empty_z_pass}, const_111_pass={all_ones_pass}, "
        f"case_ineq_fixed_Z_pass={fixed_z_pass} (errors={err_fixed_z.to_uint()}/100)"
    )
    print(
        f"  RTLLM sequence_detector empty_Z_pass={seq_empty_z_pass}; "
        f"square_wave empty_Z_pass={sq_empty_z_pass}, const_0_pass={sq_const0_pass}"
    )
    print(
        f"  Ternary `integer error` on Z vs ref=0: 4-state_bits=...{err_4state.bits[-4:]} "
        f"(pass={ternary_4state_passes}) vs 2-state_Verilator_collapse (pass={ternary_2state_passes})"
    )
    print(
        f"  RTLLM auto_run.py cal_atk(50 perfect): {func_atk:.6f} (exact 50/51, -{(1.0 - func_atk)*100:.2f}% deflation); "
        f"VerilogEval t=0 $finish -> v1='{verilog_eval_v1_grade_port(zero_sample_log)}', v2='{v2_zero_code}', sticky_v2='{v2_sticky_code}'"
    )


# ============================================================================
# Pillar 2: Exhaustive Sequential Miter Matrix (TB vs BMC vs Induct vs k-Ind)
# ============================================================================


@dataclass(frozen=True)
class SequentialMiter:
    name: str
    all_states: tuple[tuple[int, ...], ...]
    init_states: tuple[tuple[int, ...], ...]  # Symbolic $anyinit initial set
    tb_init_state: tuple[int, ...]  # Deterministic 2-state/reset TB starting state
    inputs: tuple[int, ...]
    step_fn: Callable[[tuple[int, ...], int], tuple[int, ...]]
    equiv_fn: Callable[[tuple[int, ...], int], bool]
    tb_trace: tuple[int, ...]


def check_exact_reachability(m: SequentialMiter) -> tuple[bool, int | None]:
    """Exact BFS reachability over product state space from init_states."""
    visited = set(m.init_states)
    queue: deque[tuple[tuple[int, ...], int]] = deque((s, 0) for s in m.init_states)
    while queue:
        st, depth = queue.popleft()
        for inp in m.inputs:
            if not m.equiv_fn(st, inp):
                return False, depth
            nxt = m.step_fn(st, inp)
            if nxt not in visited:
                visited.add(nxt)
                queue.append((nxt, depth + 1))
    return True, None


def check_finite_tb(m: SequentialMiter) -> tuple[bool, int | None]:
    st = m.tb_init_state
    for cyc, inp in enumerate(m.tb_trace):
        if not m.equiv_fn(st, inp):
            return False, cyc
        st = m.step_fn(st, inp)
    return True, None


def check_bmc_anyinit(
    m: SequentialMiter,
    depth: int,
    inv: Callable[[tuple[int, ...]], bool] | None = None,
) -> tuple[bool, int | None]:
    """Exact SymbiYosys sby_mode_bmc.py (default depth=20) with $anyinit.
    When `inv` is provided, also checks `inv(st)` on every reachable state across
    steps 0..depth-1 (required for sound invariant-strengthened k-induction)."""
    frontier = set(m.init_states)
    for cyc in range(depth):
        next_frontier: set[tuple[int, ...]] = set()
        for st in sorted(frontier):
            if inv is not None and not inv(st):
                return False, cyc
            for inp in m.inputs:
                if not m.equiv_fn(st, inp):
                    return False, cyc
                next_frontier.add(m.step_fn(st, inp))
        frontier = next_frontier
    return True, None


def check_yosys_equiv_induct(m: SequentialMiter, max_seq: int = 4) -> tuple[str, int]:
    """Exact port of Yosys@11d972c2 passes/equiv/equiv_induct.cc:104-136.
    Step `step` checks:
      1) Existential base case (line 116): exists state s_1 and inputs x_1..x_step
         such that equiv holds on steps 1..step.
      2) Induction step (line 126): no state s_1 and inputs x_1..x_{step+1} satisfy
         equiv on steps 1..step and violate equiv on step+1.
    Never calls satgen.setInitState (universal initial-state base case omitted)."""
    consistent_end_states = {
        m.step_fn(s, x)
        for s in m.all_states
        for x in m.inputs
        if m.equiv_fn(s, x)
    }
    for step in range(1, max_seq + 1):
        if not consistent_end_states:
            return "FAIL_BASE_UNSAT", step
        cex_found = False
        next_consistent: set[tuple[int, ...]] = set()
        for st in sorted(consistent_end_states):
            for x in m.inputs:
                if not m.equiv_fn(st, x):
                    cex_found = True
                else:
                    next_consistent.add(m.step_fn(st, x))
        if not cex_found:
            return "PROVEN", step
        consistent_end_states = next_consistent
    return "UNPROVEN", max_seq


def check_k_induction(
    m: SequentialMiter,
    k: int,
    simple_path: bool = False,
    inv: Callable[[tuple[int, ...]], bool] | None = None,
) -> str:
    """Sound k-induction (plain vs Yosys sat.cc:1507,1552 simple-path uniqueness
    + optional state invariant strengthening `inv`):
    1) Base case (steps 0..k-1 from init_states): verifies BOTH `inv(s_t)` AND
       `equiv_fn(s_t, x_t)` on all reachable states for 0 <= t < k.
    2) Inductive step (0..k-1 => k): assumes `inv(s_t)` and `equiv_fn(s_t, x_t)`
       for 0 <= t < k (and pairwise-distinct states s_0..s_k if `simple_path`),
       and proves BOTH `inv(s_k)` AND `forall x_k. equiv_fn(s_k, x_k)` at step k."""
    assert k >= 1
    ok_bmc, _ = check_bmc_anyinit(m, k, inv=inv)
    if not ok_bmc:
        return "CEX_BASE"

    def dfs(path: list[tuple[int, ...]]) -> bool:
        cur = path[-1]
        if len(path) == k + 1:
            # Step k (s_k): prove BOTH state invariant `inv(s_k)` and output equivalence!
            if inv is not None and not inv(cur):
                return False
            for x in m.inputs:
                if not m.equiv_fn(cur, x):
                    return False
            return True
        # Steps 0..k-1: `inv(cur)` already holds by hypothesis; branch on inputs satisfying equiv_fn
        for x in m.inputs:
            if not m.equiv_fn(cur, x):
                continue
            nxt = m.step_fn(cur, x)
            if simple_path and nxt in path:
                continue
            # Only assume `inv(nxt)` on intermediate prefix states s_1..s_{k-1}, NEVER on target s_k!
            if len(path) < k and inv is not None and not inv(nxt):
                continue
            path.append(nxt)
            if not dfs(path):
                return False
            path.pop()
        return True

    for s0 in m.all_states:
        if inv is not None and not inv(s0):
            continue
        if not dfs([s0]):
            return "INDUCT_FAIL"
    return "PROVEN"


def run_probe_2() -> None:
    print("========================================================================")
    print("PROBE 2: Exhaustive Sequential Miter Matrix (TB vs BMC vs equiv_induct vs k-Ind)")
    print("Provenance: [exhaustive finite-state product-miter model + pinned Yosys equiv_induct port]")

    # Circuit 1: Missing-reset shadow register (`shadow_latch` omitted from synchronous reset)
    # State = (acc_gold[0..3], acc_gate[0..3], shadow_gate[0..1])
    c1_states = tuple(itertools.product(range(4), range(4), range(2)))
    c1_init = tuple((0, 0, sh) for sh in (0, 1))  # $anyinit explores sh=1!
    c1 = SequentialMiter(
        name="C1_missing_reset_latch",
        all_states=c1_states,
        init_states=c1_init,
        tb_init_state=(0, 0, 0),  # 2-state zero-initialized TB hides sh=1
        inputs=(0, 1),
        step_fn=lambda s, x: ((s[0] + x) & 3, (s[1] + x + s[2]) & 3, s[2]),
        equiv_fn=lambda s, _x: s[0] == s[1],
        tb_trace=(1, 1, 0, 1) * 5,
    )

    # Circuit 2: 6-bit watchdog counter rollover bug at cycle t = 32 (> default sby BMC depth 20)
    # Gold increments mod 64; Gate erroneously wraps to 0 when count == 31 + 1 == 32!
    c2_all = tuple(itertools.product(range(64), range(64)))
    c2 = SequentialMiter(
        name="C2_counter6_bug_at_32",
        all_states=c2_all,
        init_states=((0, 0),),
        tb_init_state=(0, 0),
        inputs=(1,),  # Count enabled
        step_fn=lambda s, x: (
            (s[0] + x) & 63,
            0 if (s[1] == 31 and x == 1) else ((s[1] + x) & 63),
        ),
        equiv_fn=lambda s, _x: s[0] == s[1],
        tb_trace=(1,) * 20,
    )

    # Circuit 3a: Wrong power-on `initial` / `(* init *)` parity toggle register
    # (Gold initializes q=0, Gate initializes q=1; q' = q ^ in; no synchronous `rst` input port)
    c3_states = tuple(itertools.product((0, 1), (0, 1)))
    c3 = SequentialMiter(
        name="C3_wrong_init_parity",
        all_states=c3_states,
        init_states=((0, 1),),
        tb_init_state=(0, 1),
        inputs=(0, 1),
        step_fn=lambda s, x: (s[0] ^ x, s[1] ^ x),
        equiv_fn=lambda s, _x: s[0] == s[1],
        tb_trace=(0, 1, 1, 0) * 5,
    )

    # Circuit 3b: Contrast case with unconstrained synchronous `rst` primary input (inp == 2 -> rst=1)
    # where `rst=1` drives gold<=0 and gate<=1 during the inductive step, allowing equiv_induct to fail.
    c3_sync_rst = SequentialMiter(
        name="C3b_unconstrained_sync_rst",
        all_states=c3_states,
        init_states=((0, 1),),
        tb_init_state=(0, 1),
        inputs=(0, 1, 2),  # 0: in=0,rst=0; 1: in=1,rst=0; 2: rst=1
        step_fn=lambda s, x: (0, 1) if x == 2 else (s[0] ^ x, s[1] ^ x),
        equiv_fn=lambda s, _x: s[0] == s[1],
        tb_trace=(0, 1, 1, 0) * 5,
    )

    # Circuit 4: Functionally EQUIVALENT stuttering 2-bit binary vs 4-bit one-hot FSM
    # Input x = clock-enable `en` in {0, 1}; output y = (gold == 3) vs gate[3] (bit 3 of 4-bit reg)
    c4_states = tuple(itertools.product(range(4), range(16)))

    def rot_left4(v: int) -> int:
        return ((v << 1) & 0xF) | ((v >> 3) & 0x1)

    c4 = SequentialMiter(
        name="C4_stutter_bin2_vs_onehot4",
        all_states=c4_states,
        init_states=((0, 0b0001),),
        tb_init_state=(0, 0b0001),
        inputs=(0, 1),
        step_fn=lambda s, en: (
            (s[0] + 1) & 3 if en else s[0],
            rot_left4(s[1]) if en else s[1],
        ),
        equiv_fn=lambda s, _en: int(s[0] == 3) == ((s[1] >> 3) & 1),
        tb_trace=(1, 0, 1, 1, 0, 1, 1) * 3,
    )

    # Negative-control miter for k-induction soundness:
    # 2-stage delayed shadow bug agreeing at t in {0, 1} from (0, 0, 0, 1) and diverging at t = 2!
    c1_del_states = tuple(itertools.product(range(2), range(2), range(2), range(2)))
    c1_delayed = SequentialMiter(
        name="C1_delayed_2step_bug",
        all_states=c1_del_states,
        init_states=((0, 0, 0, 1),),  # (out_gold, out_gate, pipe_gate, bad_shadow=1)
        tb_init_state=(0, 0, 0, 0),
        inputs=(0, 1),
        step_fn=lambda s, x: (x, x ^ s[2], s[3], s[3]),
        equiv_fn=lambda s, _x: s[0] == s[1],
        tb_trace=(0, 1, 0, 1),
    )

    # Assertions on C1
    c1_exact, _ = check_exact_reachability(c1)
    c1_tb, _ = check_finite_tb(c1)
    c1_bmc20, c1_bmc_cyc = check_bmc_anyinit(c1, 20)
    assert c1_exact is False and c1_tb is True and c1_bmc20 is False and c1_bmc_cyc == 1

    # Assertions on C2
    c2_exact, c2_exact_cyc = check_exact_reachability(c2)
    c2_tb, _ = check_finite_tb(c2)
    c2_bmc20, _ = check_bmc_anyinit(c2, 20)
    c2_bmc35, c2_bmc35_cyc = check_bmc_anyinit(c2, 35)
    c2_ind, _ = check_yosys_equiv_induct(c2, max_seq=4)
    assert c2_exact is False and c2_exact_cyc == 32
    assert c2_tb is True and c2_bmc20 is True
    assert c2_bmc35 is False and c2_bmc35_cyc == 32
    assert c2_ind == "UNPROVEN"

    # Assertions on C3 vs C3b (power-on initial/(* init *) vs unconstrained synchronous rst port)
    c3_exact, c3_cyc = check_exact_reachability(c3)
    c3_bmc20, _ = check_bmc_anyinit(c3, 20)
    c3_ind_status, c3_ind_step = check_yosys_equiv_induct(c3, max_seq=4)
    c3b_ind_status, _ = check_yosys_equiv_induct(c3_sync_rst, max_seq=4)
    assert c3_exact is False and c3_cyc == 0 and c3_bmc20 is False
    assert c3_ind_status == "PROVEN" and c3_ind_step == 1
    assert c3b_ind_status == "UNPROVEN"

    # Assertions on C4 (stuttering re-encoded FSM completeness hierarchy)
    c4_exact, _ = check_exact_reachability(c4)
    assert c4_exact is True
    for k in range(1, 7):
        assert check_k_induction(c4, k, simple_path=False) == "INDUCT_FAIL"
    assert check_k_induction(c4, 3, simple_path=True, inv=None) == "INDUCT_FAIL"
    is_onehot = lambda s: s[1] in (0b0001, 0b0010, 0b0100, 0b1000)
    enc_map = lambda s: s[1] == (1 << s[0])
    assert check_k_induction(c4, 2, simple_path=True, inv=is_onehot) == "INDUCT_FAIL"
    assert check_k_induction(c4, 3, simple_path=True, inv=is_onehot) == "PROVEN"
    assert check_k_induction(c4, 1, simple_path=False, inv=enc_map) == "PROVEN"

    # Negative-control assertions proving check_k_induction soundness on false/non-initial/non-inductive invariants
    c1d_exact, c1d_cyc = check_exact_reachability(c1_delayed)
    assert c1d_exact is False and c1d_cyc == 2
    assert check_k_induction(c2, 1, simple_path=False, inv=lambda _s: False) == "CEX_BASE"
    assert (
        check_k_induction(
            c1_delayed, 1, simple_path=False, inv=lambda s: s[3] == 0 and s[0] == s[1]
        )
        == "CEX_BASE"
    )
    assert (
        check_k_induction(
            c1_delayed, 1, simple_path=False, inv=lambda s: s[2] == 0 and s[0] == s[1]
        )
        == "INDUCT_FAIL"
    )
    assert (
        check_k_induction(
            c1_delayed, 2, simple_path=False, inv=lambda s: s[2] == 0 and s[0] == s[1]
        )
        == "CEX_BASE"
    )

    print(
        f"  {c1.name}: exact_equiv={c1_exact}, 2state_tb={c1_tb} (FALSE PASS), "
        f"bmc_anyinit(20)={c1_bmc20} (caught at t={c1_bmc_cyc})"
    )
    print(
        f"  {c2.name}: exact_equiv={c2_exact} (t={c2_exact_cyc}), tb(20)={c2_tb} (FALSE PASS), "
        f"bmc(20)={c2_bmc20} (FALSE PASS), bmc(35)={c2_bmc35} (caught at t={c2_bmc35_cyc}), equiv_induct={c2_ind}"
    )
    print(
        f"  {c3.name}: exact_equiv={c3_exact} (t={c3_cyc}), bmc(20)={c3_bmc20}, "
        f"standalone equiv_induct={c3_ind_status} at step={c3_ind_step} (UNSOUND on initial/(* init *); "
        f"unconstrained sync rst={c3b_ind_status})"
    )
    print(
        f"  {c4.name}: exact_equiv={c4_exact}, plain_k_ind(k=1..6)=INDUCT_FAIL, "
        f"simple_path(k=3,no_inv)=INDUCT_FAIL (4'b0000 dead trap), "
        f"simple_path(k=3,$onehot)=PROVEN, encfile_inv(k=1)=PROVEN "
        f"[neg_controls: false_inv=CEX_BASE, non_ind_inv=INDUCT_FAIL]"
    )


# ============================================================================
# Pillar 3: Yosys@11d972c2 SatGen Dual-Rail Kleene / State::Sz & Miter/SAT Gates
# ============================================================================


@dataclass(frozen=True)
class YosysSig:
    """Models a 1-bit Yosys RTLIL SigBit under SatGen (kernel/satgen.h:100-105, 270-285):
    - kind == 'const': literal RTLIL::State::S0 ('0'), S1 ('1'), Sx ('X'), or Sz ('Z')
      with bit.wire == NULL.
    - kind == 'wire' : driven cell wire with 3-valued Kleene state ('0', '1', 'X')."""

    kind: str  # 'const' or 'wire'
    val: str  # '0', '1', 'X', or ('Z' when kind == 'const')

    def __post_init__(self) -> None:
        assert self.kind in ("const", "wire")
        if self.kind == "const":
            assert self.val in ("0", "1", "X", "Z")
        else:
            assert self.val in ("0", "1", "X")


def satgen_import_sig(
    sig: YosysSig, model_undef: bool, dup_undef: bool
) -> list[tuple[int, int]]:
    """Exact port of SatGen::importSigSpecWorker (kernel/satgen.h:100-105) and
    SatGen::undefGating (kernel/satgen.h:282-285), returning all (val, undef) pairs
    satisfying the imported SAT constraints."""
    if sig.kind == "const":
        if sig.val == "0":
            return [(0, 0)]
        if sig.val == "1":
            return [(1, 0)]
        if sig.val == "Z":
            # kernel/satgen.h:101-104: bit == State::Sx is FALSE and bit == State::S1
            # is FALSE, so literal State::Sz ('1'bz) is coerced to (val=0, undef=0)
            # EVEN WHEN model_undef=True and dup_undef=True!
            return [(0, 0)]
        # sig.val == 'X' (RTLIL::State::Sx):
        if model_undef and dup_undef:
            return [(0, 1), (1, 1)]
        return [(0, 1 if model_undef else 0)]
    # Driven cell wire:
    if sig.val == "0":
        return [(0, 0)]
    if sig.val == "1":
        return [(1, 0)]
    return [(0, 1 if model_undef else 0), (1, 1 if model_undef else 0)]


def yosys_setundef_undef_pass(sig: YosysSig) -> YosysSig:
    """Port of `setundef -undef` (passes/cmds/setundef.cc:105-107, 199-204):
    rewrites any literal bit with `bit.wire == NULL && bit.data > State::S1`
    (including State::Sz) to State::Sx."""
    if sig.kind == "const" and sig.val in ("X", "Z"):
        return YosysSig("const", "X")
    return sig


def satgen_eval_not(
    a_pairs: list[tuple[int, int]], model_undef: bool
) -> list[tuple[int, int]]:
    out: set[tuple[int, int]] = set()
    for va, ua in a_pairs:
        if not model_undef or ua == 0:
            out.add((1 - va, 0))
        else:
            out.add((0, 1))
            out.add((1, 1))
    return sorted(out)


def satgen_eval_and(
    a_pairs: list[tuple[int, int]], b_pairs: list[tuple[int, int]], model_undef: bool
) -> list[tuple[int, int]]:
    """Exact port of SatGen::importCell for $and/$_AND_ (kernel/satgen.cc:72-73, 100-105)."""
    out: set[tuple[int, int]] = set()
    for (va, ua), (vb, ub) in itertools.product(a_pairs, b_pairs):
        yy = va & vb
        if not model_undef:
            out.add((yy, 0))
            continue
        a0 = (1 - va) & (1 - ua)
        b0 = (1 - vb) & (1 - ub)
        uy = (ua | ub) & (1 - (a0 | b0))
        if uy == 1:
            out.add((0, 1))
            out.add((1, 1))
        else:
            out.add((yy, 0))
    return sorted(out)


def satgen_eval_or(
    a_pairs: list[tuple[int, int]], b_pairs: list[tuple[int, int]], model_undef: bool
) -> list[tuple[int, int]]:
    """Exact port of SatGen::importCell for $or/$_OR_ (kernel/satgen.cc:76-77, 106-111)."""
    out: set[tuple[int, int]] = set()
    for (va, ua), (vb, ub) in itertools.product(a_pairs, b_pairs):
        yy = va | vb
        if not model_undef:
            out.add((yy, 0))
            continue
        a1 = va & (1 - ua)
        b1 = vb & (1 - ub)
        uy = (ua | ub) & (1 - (a1 | b1))
        if uy == 1:
            out.add((0, 1))
            out.add((1, 1))
        else:
            out.add((yy, 0))
    return sorted(out)


def satgen_eval_mux(
    s_pairs: list[tuple[int, int]],
    a_pairs: list[tuple[int, int]],
    b_pairs: list[tuple[int, int]],
    model_undef: bool,
) -> list[tuple[int, int]]:
    """Exact port of SatGen::mux + undefGating (kernel/satgen.h:270-285):
    Y = S ? B : A."""
    out: set[tuple[int, int]] = set()
    for (vs, us), (va, ua), (vb, ub) in itertools.product(s_pairs, a_pairs, b_pairs):
        res = vb if vs == 1 else va
        if not model_undef:
            out.add((res, 0))
            continue
        unequal_ab = 1 if (va != vb) else 0
        undef_ab = unequal_ab | ua | ub
        uy = undef_ab if us == 1 else (ub if vs == 1 else ua)
        if uy == 1:
            out.add((0, 1))
            out.add((1, 1))
        else:
            out.add((res, 0))
    return sorted(out)


def satgen_eval_eqx(
    a_pairs: list[tuple[int, int]], b_pairs: list[tuple[int, int]], model_undef: bool
) -> list[tuple[int, int]]:
    """Exact port of SatGen::importCell for $eqx (kernel/satgen.cc:561-610)."""
    out: set[tuple[int, int]] = set()
    for (va, ua), (vb, ub) in itertools.product(a_pairs, b_pairs):
        if not model_undef:
            # Lines 571-577 and 594-610 are skipped when model_undef == false!
            out.add((1 if va == vb else 0, 0))
        else:
            a_eff = va | ua
            b_eff = vb | ub
            yy = 1 if (a_eff == b_eff and ua == ub) else 0
            out.add((yy, 0))
    return sorted(out)


def satgen_eval_miter_equiv(
    gold: YosysSig,
    gate: YosysSig,
    ignore_gold_x: bool,
    enable_undef: bool,
    flatten: bool = True,
) -> str:
    """Evaluates `miter -equiv [-flatten] [-ignore_gold_x] -make_assert`
    (passes/sat/miter.cc:33, 137-138, 182-243, 291-295) followed by
    `sat -verify -prove-asserts [-set-def-inputs]` (passes/sat/sat.cc:1108, 1182-1185, 1254).
    Returns 'ERROR_UNFLATTENED_CELL', 'PROVEN', or 'FAIL'."""
    if not flatten:
        # miter.cc:33, 137-138: without -flatten, \gold and \gate remain unflattened
        # user-module cells and sat fails on unknown cell types.
        return "ERROR_UNFLATTENED_CELL"

    w_gold = satgen_import_sig(gold, enable_undef, dup_undef=True)
    w_gate = satgen_import_sig(gate, enable_undef, dup_undef=True)
    sx_lit = satgen_import_sig(YosysSig("const", "X"), enable_undef, dup_undef=True)

    for g_pair, b_pair in itertools.product(w_gold, w_gate):
        if ignore_gold_x:
            for sx_pair in sx_lit:
                gold_x = satgen_eval_eqx([g_pair], [sx_pair], enable_undef)
                gold_m = satgen_eval_or([g_pair], gold_x, enable_undef)
                gate_m = satgen_eval_or([b_pair], gold_x, enable_undef)
                conds = satgen_eval_eqx(gold_m, gate_m, enable_undef)
                if any(v == 0 for v, _u in conds):
                    return "FAIL"
        else:
            conds = satgen_eval_eqx([g_pair], [b_pair], enable_undef)
            if any(v == 0 for v, _u in conds):
                return "FAIL"
    return "PROVEN"


def yosys_eval_equiv_modes(gold: YosysSig, gate: YosysSig) -> dict[str, bool]:
    """Exact SAT-unsat (True = proven equivalent, False = counterexample exists)
    across 7 Yosys@11d972c2 equivalence encodings for a single observation point."""
    # 1. equiv_induct default (equiv.h:13 model_undef=false, equiv_induct.cc:56 IFF(ez_a, ez_b))
    ind_def_ok = all(
        va == vb
        for (va, _), (vb, _) in itertools.product(
            satgen_import_sig(gold, False, False), satgen_import_sig(gate, False, False)
        )
    )

    # 2. equiv_induct -undef main loop (equiv_induct.cc:56-60: undef_a || (!undef_b && (va == vb)))
    ind_undef_ok = all(
        (ua == 1) or (ub == 0 and va == vb)
        for (va, ua), (vb, ub) in itertools.product(
            satgen_import_sig(gold, True, False), satgen_import_sig(gate, True, False)
        )
    )

    # 3. equiv_induct -undef per-cell fallback (equiv_induct.cc:146-153:
    #    cond = AND(XOR(importSigBit(a), importSigBit(b)), NOT(undef_a)); proven if !solve(cond))
    ind_fallback_ok = not any(
        (ua == 0) and (va ^ vb == 1)
        for (va, ua), (vb, _ub) in itertools.product(
            satgen_import_sig(gold, True, False), satgen_import_sig(gate, True, False)
        )
    )

    # 4. equiv_simple -undef (equiv_simple.cc:256-261 uses importDefSigBit on bit_b!)
    simple_undef_ok = not any(
        (ua == 0) and (va ^ vb == 1)
        for (va, ua), (vb, _ub) in itertools.product(
            satgen_import_sig(gold, True, False), satgen_import_sig(gate, True, True)
        )
    )

    # 5. Symmetric $eqx (`miter -equiv -flatten -make_assert` + `sat -verify -prove-asserts -set-def-inputs`)
    eqx_sym_ok = (
        satgen_eval_miter_equiv(
            gold, gate, ignore_gold_x=False, enable_undef=True, flatten=True
        )
        == "PROVEN"
    )

    # 6. UNSOUND `miter -equiv -flatten -ignore_gold_x -make_assert` + `sat -verify -prove-asserts`
    #    WITHOUT `-set-def-inputs` / `-enable_undef` (enable_undef=False -> $eqx(gold, Sx) becomes gold==0!)
    miter_no_undef_ok = (
        satgen_eval_miter_equiv(
            gold, gate, ignore_gold_x=True, enable_undef=False, flatten=True
        )
        == "PROVEN"
    )

    # 7. SOUND `miter -equiv -flatten -ignore_gold_x -make_assert` + `sat -verify -prove-asserts -set-def-inputs`
    miter_set_def_ok = (
        satgen_eval_miter_equiv(
            gold, gate, ignore_gold_x=True, enable_undef=True, flatten=True
        )
        == "PROVEN"
    )

    return {
        "equiv_induct_default": ind_def_ok,
        "equiv_induct_undef": ind_undef_ok,
        "equiv_induct_undef_fallback": ind_fallback_ok,
        "equiv_simple_undef": simple_undef_ok,
        "symmetric_eqx": eqx_sym_ok,
        "miter_sat_no_undef": miter_no_undef_ok,
        "miter_sat_set_def_inputs": miter_set_def_ok,
    }


def check_mux_decomp_under_input_undef(set_def_inputs: bool) -> bool:
    """Checks `gold`: $mux(s, d, d) vs `gate`: (s & d) | (~s & d) under
    `miter -equiv -flatten -ignore_gold_x -make_assert` + `sat -verify -prove-asserts`
    comparing bare `-enable_undef` (`set_def_inputs=False`) against `-set-def-inputs` (`True`)."""
    in_domain = [(0, 0), (1, 0)] if set_def_inputs else [(0, 0), (1, 0), (0, 1), (1, 1)]
    sx_lit = satgen_import_sig(YosysSig("const", "X"), True, dup_undef=True)
    for s_pair, d_pair in itertools.product(in_domain, in_domain):
        gold_out = satgen_eval_mux([s_pair], [d_pair], [d_pair], model_undef=True)
        not_s = satgen_eval_not([s_pair], model_undef=True)
        t1 = satgen_eval_and([s_pair], [d_pair], model_undef=True)
        t2 = satgen_eval_and(not_s, [d_pair], model_undef=True)
        gate_out = satgen_eval_or(t1, t2, model_undef=True)
        for g_p, b_p, sx_p in itertools.product(gold_out, gate_out, sx_lit):
            gold_x = satgen_eval_eqx([g_p], [sx_p], model_undef=True)
            gold_m = satgen_eval_or([g_p], gold_x, model_undef=True)
            gate_m = satgen_eval_or([b_p], gold_x, model_undef=True)
            if any(v == 0 for v, _u in satgen_eval_eqx(gold_m, gate_m, model_undef=True)):
                return False
    return True


def run_probe_3() -> None:
    print("========================================================================")
    print("PROBE 3: Yosys@11d972c2 SatGen Kleene/`State::Sz` & Miter/SAT Encodings")
    print("Provenance: [pinned Yosys SatGen 3-valued Kleene + literal State::Sx/Sz port]")

    # Unflattened `miter -equiv` without `-flatten` rejects user submodule cells
    assert (
        satgen_eval_miter_equiv(
            YosysSig("wire", "0"),
            YosysSig("wire", "0"),
            ignore_gold_x=True,
            enable_undef=True,
            flatten=False,
        )
        == "ERROR_UNFLATTENED_CELL"
    )

    # Case A: Valid synthesis don't-care optimization (gold = X on unused opcode -> gate = 0)
    case_a = yosys_eval_equiv_modes(YosysSig("wire", "X"), YosysSig("wire", "0"))
    assert case_a["symmetric_eqx"] is False  # False rejection of valid synthesis!
    assert case_a["equiv_induct_undef"] is True
    assert case_a["equiv_simple_undef"] is True
    assert case_a["miter_sat_set_def_inputs"] is True

    # Case B: Buggy gate mux leaks dynamic X wire when gold drives 1
    case_b = yosys_eval_equiv_modes(YosysSig("wire", "1"), YosysSig("wire", "X"))
    assert case_b["equiv_induct_undef"] is False
    assert case_b["equiv_simple_undef"] is False
    assert case_b["miter_sat_set_def_inputs"] is False

    # Case C: Buggy gate leaves output undriven (wired to literal State::Sx by equiv_make.cc:415)
    # while gold outputs constant 0!
    case_c = yosys_eval_equiv_modes(YosysSig("const", "0"), YosysSig("const", "X"))
    assert case_c["equiv_induct_default"] is True  # Unsoundly accepts due to State::Sx -> CONST_FALSE!
    assert case_c["equiv_induct_undef_fallback"] is True  # Fallback loop omits undef_b + dup_undef!
    assert case_c["equiv_induct_undef"] is False  # Main loop catches undef_b!
    assert case_c["equiv_simple_undef"] is False  # importDefSigBit catches literal Sx!
    assert case_c["miter_sat_set_def_inputs"] is False

    # Case D: Blatant Boolean bug (gold = 0 vs gate = 1) exposing catastrophic `sat` unsoundness
    # when `-set-def-inputs` / `-enable_undef` is omitted on `miter -equiv -ignore_gold_x`!
    case_d = yosys_eval_equiv_modes(YosysSig("wire", "0"), YosysSig("wire", "1"))
    assert case_d["miter_sat_no_undef"] is True  # UNSOUND: $eqx(gold, Sx) compiles to gold == 0!
    assert case_d["miter_sat_set_def_inputs"] is False  # Soundly caught with -set-def-inputs!
    assert case_d["equiv_simple_undef"] is False

    # Case E: Explicit tri-state literal `assign y = 1'bz;` (RTLIL::State::Sz) vs gold = 0:
    # SatGen coerces literal State::Sz to (0, 0) even with -undef / -set-def-inputs unless
    # `setundef -undef` normalizes State::Sz -> State::Sx first!
    case_e_raw = yosys_eval_equiv_modes(YosysSig("const", "0"), YosysSig("const", "Z"))
    case_e_norm = yosys_eval_equiv_modes(
        YosysSig("const", "0"), yosys_setundef_undef_pass(YosysSig("const", "Z"))
    )
    assert case_e_raw["equiv_simple_undef"] is True and case_e_raw["miter_sat_set_def_inputs"] is True
    assert case_e_norm["equiv_simple_undef"] is False and case_e_norm["miter_sat_set_def_inputs"] is False

    # Case F: Bare `-enable_undef` without `-set-def-inputs` falsely rejects valid gate mux decomposition
    mux_bare_undef_ok = check_mux_decomp_under_input_undef(set_def_inputs=False)
    mux_set_def_in_ok = check_mux_decomp_under_input_undef(set_def_inputs=True)
    assert mux_bare_undef_ok is False and mux_set_def_in_ok is True

    print(
        f"  Case A (valid don't-care gold=X -> gate=0): "
        f"symmetric_$eqx={case_a['symmetric_eqx']} (FALSE REJECT), "
        f"equiv_simple_-undef={case_a['equiv_simple_undef']}, miter_sat_-set-def-inputs={case_a['miter_sat_set_def_inputs']}"
    )
    print(
        f"  Case B (gate mux X-leak gold=1 -> gate=wire_X): "
        f"equiv_induct_-undef={case_b['equiv_induct_undef']}, "
        f"equiv_simple_-undef={case_b['equiv_simple_undef']}, miter_sat_-set-def-inputs={case_b['miter_sat_set_def_inputs']}"
    )
    print(
        f"  Case C (undriven gate State::Sx vs gold=0): "
        f"induct_default={case_c['equiv_induct_default']} (UNSOUND), "
        f"induct_undef_fallback={case_c['equiv_induct_undef_fallback']} (UNSOUND), "
        f"simple_undef={case_c['equiv_simple_undef']}, miter_sat_-set-def-inputs={case_c['miter_sat_set_def_inputs']}"
    )
    print(
        f"  Case D/E/F (`sat` & `State::Sz` traps): "
        f"miter_no_undef(gold=0,gate=1)={case_d['miter_sat_no_undef']} (UNSOUND vs -set-def-inputs={case_d['miter_sat_set_def_inputs']}); "
        f"State::Sz_raw={case_e_raw['miter_sat_set_def_inputs']} (UNSOUND vs setundef_-undef={case_e_norm['miter_sat_set_def_inputs']}); "
        f"mux_bare_-enable_undef={mux_bare_undef_ok} (FALSE REJECT vs -set-def-inputs={mux_set_def_in_ok})"
    )


# ============================================================================
# Pillar 4: Structural AIG Area vs Critical-Path Depth Pareto (`BetterV` Trap)
# ============================================================================


class AIG:
    """Structural-hashed And-Inverter Graph (optional strash toggle to compare
    raw `proc; aigmap` vs `strash` node counts, unit-delay depth, gate fanout,
    and bit-slice horizontal wire-span congestion)."""

    def __init__(self, strash: bool = True) -> None:
        self.strash = strash
        self.num_pis = 0
        # Node id >= 1: (lit0, lit1) for AND gate, or None for PI.
        # Literal encoding: lit = 2 * var_id ^ inv (0 = const0, 1 = const1).
        self.nodes: list[tuple[int, int] | None] = [None]  # index 0 = const0
        self.node_col: list[int] = [0]
        self.cur_col: int = 0
        self.hash_tab: dict[tuple[int, int], int] = {}

    def set_col(self, col: int) -> None:
        self.cur_col = col

    def const0(self) -> int:
        return 0

    def const1(self) -> int:
        return 1

    def pi(self, col: int = 0) -> int:
        self.num_pis += 1
        var_id = len(self.nodes)
        self.nodes.append(None)
        self.node_col.append(col)
        return var_id << 1

    @staticmethod
    def not_(lit: int) -> int:
        return lit ^ 1

    def and_(self, a: int, b: int) -> int:
        if self.strash:
            if a == 0 or b == 0:
                return 0
            if a == 1:
                return b
            if b == 1:
                return a
            if a == b:
                return a
            if a == (b ^ 1):
                return 0
            if a > b:
                a, b = b, a
            hit = self.hash_tab.get((a, b))
            if hit is not None:
                return hit
        var_id = len(self.nodes)
        self.nodes.append((a, b))
        self.node_col.append(self.cur_col)
        lit = var_id << 1
        if self.strash:
            self.hash_tab[(a, b)] = lit
        return lit

    def or_(self, a: int, b: int) -> int:
        return self.not_(self.and_(self.not_(a), self.not_(b)))

    def xor_(self, a: int, b: int) -> int:
        return self.or_(self.and_(a, self.not_(b)), self.and_(self.not_(a), b))

    def mux_(self, sel: int, if1: int, if0: int) -> int:
        return self.or_(self.and_(sel, if1), self.and_(self.not_(sel), if0))

    def stats(
        self, outputs: list[int], alpha_fo: float = 0.35, beta_span: float = 0.12
    ) -> dict[str, float | int]:
        """Computes active AND-node count, unit-delay critical depth, max gate fanout,
        total horizontal inter-column wire span, and physical RC/fanout delay."""
        active: set[int] = set()
        stack = [lit >> 1 for lit in outputs if (lit >> 1) > 0]
        while stack:
            v = stack.pop()
            if v in active or self.nodes[v] is None:
                continue
            active.add(v)
            c0, c1 = self.nodes[v]  # type: ignore[misc]
            if (c0 >> 1) > 0:
                stack.append(c0 >> 1)
            if (c1 >> 1) > 0:
                stack.append(c1 >> 1)

        fanout: dict[int, int] = {v: 0 for v in range(len(self.nodes))}
        total_wire_span = 0
        for v in sorted(active):
            c0, c1 = self.nodes[v]  # type: ignore[misc]
            v0, v1 = c0 >> 1, c1 >> 1
            fanout[v0] += 1
            fanout[v1] += 1
            if v0 > 0:
                total_wire_span += abs(self.node_col[v] - self.node_col[v0])
            if v1 > 0:
                total_wire_span += abs(self.node_col[v] - self.node_col[v1])
        for lit in outputs:
            fanout[lit >> 1] += 1

        unit_depth = [0] * len(self.nodes)
        fo_delay = [0.0] * len(self.nodes)
        phys_delay = [0.0] * len(self.nodes)
        for v in range(1, len(self.nodes)):
            if v not in active:
                continue
            c0, c1 = self.nodes[v]  # type: ignore[misc]
            v0, v1 = c0 >> 1, c1 >> 1
            unit_depth[v] = 1 + max(unit_depth[v0], unit_depth[v1])
            span0 = abs(self.node_col[v] - self.node_col[v0]) if v0 > 0 else 0
            span1 = abs(self.node_col[v] - self.node_col[v1]) if v1 > 0 else 0
            fo0 = alpha_fo * max(0, fanout[v0] - 1)
            fo1 = alpha_fo * max(0, fanout[v1] - 1)
            fo_delay[v] = max(fo_delay[v0] + 1.0 + fo0, fo_delay[v1] + 1.0 + fo1)
            phys_delay[v] = max(
                phys_delay[v0] + 1.0 + fo0 + beta_span * span0,
                phys_delay[v1] + 1.0 + fo1 + beta_span * span1,
            )

        max_depth = max((unit_depth[lit >> 1] for lit in outputs), default=0)
        max_fo_d = max((fo_delay[lit >> 1] for lit in outputs), default=0.0)
        max_phys = max((phys_delay[lit >> 1] for lit in outputs), default=0.0)
        max_gate_fo = max((fanout[v] for v in active), default=0)
        return {
            "and_nodes": len(active),
            "depth": max_depth,
            "max_fanout": max_gate_fo,
            "wire_span": total_wire_span,
            "fo_delay": round(max_fo_d, 2),
            "phys_delay": round(max_phys, 2),
        }

    def eval_bitparallel(self, pi_masks: list[int], outputs: list[int], n_vecs: int) -> list[int]:
        """Evaluates all `n_vecs` input vectors in parallel using Python big-int bitmasks."""
        all_ones = (1 << n_vecs) - 1
        vals = [0] * len(self.nodes)
        pi_idx = 0
        for v in range(1, len(self.nodes)):
            node = self.nodes[v]
            if node is None:
                vals[v] = pi_masks[pi_idx]
                pi_idx += 1
            else:
                c0, c1 = node
                m0 = (vals[c0 >> 1] ^ all_ones) if (c0 & 1) else vals[c0 >> 1]
                m1 = (vals[c1 >> 1] ^ all_ones) if (c1 & 1) else vals[c1 >> 1]
                vals[v] = m0 & m1
        return [
            (vals[lit >> 1] ^ all_ones) if (lit & 1) else vals[lit >> 1]
            for lit in outputs
        ]


def build_rca(aig: AIG, a: list[int], b: list[int], cin: int) -> list[int]:
    """W-bit Ripple-Carry Adder returning [s_0, ..., s_{W-1}, cout]."""
    c = cin
    sums: list[int] = []
    for idx, (ai, bi) in enumerate(zip(a, b)):
        aig.set_col(idx)
        p = aig.xor_(ai, bi)
        g = aig.and_(ai, bi)
        sums.append(aig.xor_(p, c))
        c = aig.or_(g, aig.and_(p, c))
    sums.append(c)
    return sums


def build_kogge_stone(aig: AIG, a: list[int], b: list[int], cin: int) -> list[int]:
    """W-bit Kogge-Stone Parallel-Prefix Adder: min unit depth, O(log W) unbuffered
    AIG gate fanout (log2(W)+2 = 8 on g[0] at W=64 without per-row pass-through
    buffers), and maximum O(W^2) horizontal wire-span congestion (W^2-1 = 4095 at W=64)."""
    w = len(a)
    p0: list[int] = []
    g0: list[int] = []
    for i, (ai, bi) in enumerate(zip(a, b)):
        aig.set_col(i)
        p0.append(aig.xor_(ai, bi))
        g0.append(aig.and_(ai, bi))
    g = list(g0)
    p = list(p0)
    aig.set_col(0)
    g[0] = aig.or_(g0[0], aig.and_(p0[0], cin))
    p[0] = aig.const0()

    stride = 1
    while stride < w:
        ng = list(g)
        np = list(p)
        for i in range(stride, w):
            aig.set_col(i)
            ng[i] = aig.or_(g[i], aig.and_(p[i], g[i - stride]))
            np[i] = aig.and_(p[i], p[i - stride])
        g, p = ng, np
        stride <<= 1

    carries = [cin] + g[: w - 1]
    sums: list[int] = []
    for i in range(w):
        aig.set_col(i)
        sums.append(aig.xor_(p0[i], carries[i]))
    sums.append(g[w - 1])
    return sums


def build_sklansky(aig: AIG, a: list[int], b: list[int], cin: int) -> list[int]:
    """W-bit Sklansky Divide-and-Conquer Prefix Adder: min unit depth, fewer prefix
    nodes than Kogge-Stone, but O(W) high gate fanout at block-MSB spine nodes."""
    w = len(a)
    assert w >= 2 and (w & (w - 1)) == 0
    p0: list[int] = []
    g0: list[int] = []
    for i, (ai, bi) in enumerate(zip(a, b)):
        aig.set_col(i)
        p0.append(aig.xor_(ai, bi))
        g0.append(aig.and_(ai, bi))
    g = list(g0)
    p = list(p0)
    aig.set_col(0)
    g[0] = aig.or_(g0[0], aig.and_(p0[0], cin))
    p[0] = aig.const0()

    half = 1
    while half < w:
        block = half << 1
        for base in range(0, w, block):
            spine = base + half - 1
            g_spine, p_spine = g[spine], p[spine]
            for i in range(base + half, base + block):
                aig.set_col(i)
                g[i] = aig.or_(g[i], aig.and_(p[i], g_spine))
                p[i] = aig.and_(p[i], p_spine)
        half = block

    carries = [cin] + g[: w - 1]
    sums: list[int] = []
    for i in range(w):
        aig.set_col(i)
        sums.append(aig.xor_(p0[i], carries[i]))
    sums.append(g[w - 1])
    return sums


def build_brent_kung(aig: AIG, a: list[int], b: list[int], cin: int) -> list[int]:
    """W-bit Brent-Kung Parallel-Prefix Adder: O(log W) unbuffered AIG gate fanout
    (log2(W)+2 = 8 on g[W/2-1] at W=64 without pass-through buffers) AND O(W) wire span."""
    w = len(a)
    assert w >= 2 and (w & (w - 1)) == 0
    p0: list[int] = []
    g0: list[int] = []
    for i, (ai, bi) in enumerate(zip(a, b)):
        aig.set_col(i)
        p0.append(aig.xor_(ai, bi))
        g0.append(aig.and_(ai, bi))
    g = list(g0)
    p = list(p0)
    aig.set_col(0)
    g[0] = aig.or_(g0[0], aig.and_(p0[0], cin))
    p[0] = aig.const0()

    # Up-sweep (reduce) tree
    step = 1
    while step < w:
        span = step << 1
        for i in range(span - 1, w, span):
            j = i - step
            aig.set_col(i)
            g[i] = aig.or_(g[i], aig.and_(p[i], g[j]))
            p[i] = aig.and_(p[i], p[j])
        step = span

    # Down-sweep (distribute) tree
    step = w >> 2
    while step >= 1:
        span = step << 1
        for i in range(span + step - 1, w, span):
            j = i - step
            aig.set_col(i)
            g[i] = aig.or_(g[i], aig.and_(p[i], g[j]))
            p[i] = aig.and_(p[i], p[j])
        step >>= 1

    carries = [cin] + g[: w - 1]
    sums: list[int] = []
    for i in range(w):
        aig.set_col(i)
        sums.append(aig.xor_(p0[i], carries[i]))
    sums.append(g[w - 1])
    return sums


def make_exhaustive_adder_masks(w: int) -> tuple[list[int], int]:
    """Constructs exact bit-parallel truth-table masks for all 2^(2W+1) (a, b, cin) inputs."""
    total_bits = 2 * w + 1
    n_vecs = 1 << total_bits
    all_ones = (1 << n_vecs) - 1
    masks: list[int] = []
    for bit_idx in range(total_bits):
        period = 1 << bit_idx
        block = ((1 << period) - 1) << period
        step = period << 1
        m = block
        cur_len = step
        while cur_len < n_vecs:
            m |= m << cur_len
            cur_len <<= 1
        masks.append(m & all_ones)
    return masks, n_vecs


def verify_adder_sampled_against_int(
    w: int,
    builders: tuple[
        tuple[str, Callable[[AIG, list[int], list[int], int], list[int]]], ...
    ],
    n_samples: int = 2048,
) -> None:
    """Bit-parallel verification of all adder topologies at width `w` against exact
    Python integer `a + b + cin` over corner + deterministic random vectors."""
    rng = random.Random(0xA16000 + w)
    w_mask = (1 << w) - 1
    half = (1 << (w - 1)) - 1
    corners = [
        (0, 0, 0),
        (0, 0, 1),
        (w_mask, 0, 1),
        (0, w_mask, 1),
        (w_mask, w_mask, 0),
        (w_mask, w_mask, 1),
        (half, 1, 0),
        (1 << (w - 1), 1 << (w - 1), 0),
    ]
    vecs = list(corners)
    while len(vecs) < n_samples:
        vecs.append((rng.getrandbits(w), rng.getrandbits(w), rng.getrandbits(1)))

    pi_masks = [0] * (2 * w + 1)
    exp_masks = [0] * (w + 1)
    for idx, (va, vb, vc) in enumerate(vecs):
        bit = 1 << idx
        s = va + vb + vc
        for i in range(w):
            if (va >> i) & 1:
                pi_masks[i] |= bit
            if (vb >> i) & 1:
                pi_masks[w + i] |= bit
            if (s >> i) & 1:
                exp_masks[i] |= bit
        if vc:
            pi_masks[2 * w] |= bit
        if (s >> w) & 1:
            exp_masks[w] |= bit

    for _arch, builder in builders:
        g = AIG(strash=True)
        a_pis = [g.pi(i) for i in range(w)]
        b_pis = [g.pi(i) for i in range(w)]
        cin_pi = g.pi(0)
        out_lits = builder(g, a_pis, b_pis, cin_pi)
        got = g.eval_bitparallel(pi_masks, out_lits, len(vecs))
        assert got == exp_masks


def run_probe_4() -> None:
    print("========================================================================")
    print("PROBE 4: Adder AIG Node-Count vs Critical-Path Depth Pareto (`BetterV` Trap)")
    print("Provenance: [derived structural-hashed AIG + parameterized fanout/wire-span delay model]")

    # 1. Raw unshared `proc; aigmap` vs `strash` on unrolled priority-mux encoder (8-bit)
    for strash_flag in (False, True):
        g = AIG(strash=strash_flag)
        req = [g.pi(i) for i in range(8)]
        out = [g.const0() for _ in range(3)]
        for idx in range(8):
            higher_any = g.const0()
            for h in range(idx + 1, 8):
                higher_any = g.or_(higher_any, req[h])
            win = g.and_(req[idx], g.not_(higher_any))
            for b in range(3):
                if (idx >> b) & 1:
                    out[b] = g.or_(out[b], win)
        if not strash_flag:
            raw_mux_stats = g.stats(out)
        else:
            strash_mux_stats = g.stats(out)
    assert raw_mux_stats["and_nodes"] > strash_mux_stats["and_nodes"]

    arch_builders = (
        ("RCA", build_rca),
        ("BKA", build_brent_kung),
        ("SKA", build_sklansky),
        ("KSA", build_kogge_stone),
    )

    # 2. Exact exhaustive equivalence check at W = 8 across RCA, BKA, SKA, KSA (131,072 inputs)
    #    plus 2,048-vector corner+random integer `a + b + cin` verification at W in {16, 32, 64}
    masks8, n8 = make_exhaustive_adder_masks(8)
    outs8: dict[str, list[int]] = {}
    for arch, builder in arch_builders:
        g = AIG(strash=True)
        a_pis = [g.pi(i) for i in range(8)]
        b_pis = [g.pi(i) for i in range(8)]
        cin_pi = g.pi(0)
        out_lits = builder(g, a_pis, b_pis, cin_pi)
        outs8[arch] = g.eval_bitparallel(masks8, out_lits, n8)
    assert outs8["RCA"] == outs8["BKA"] == outs8["SKA"] == outs8["KSA"]
    for w_chk in (16, 32, 64):
        verify_adder_sampled_against_int(w_chk, arch_builders, n_samples=2048)

    # 3. Scaling table across W in {8, 16, 32, 64}
    rows: dict[int, dict[str, dict[str, float | int]]] = {}
    for w in (8, 16, 32, 64):
        rows[w] = {}
        for arch, builder in arch_builders:
            g = AIG(strash=True)
            a = [g.pi(i) for i in range(w)]
            b = [g.pi(i) for i in range(w)]
            cin = g.pi(0)
            out_lits = builder(g, a, b, cin)
            rows[w][arch] = g.stats(out_lits, alpha_fo=0.35, beta_span=0.12)

    # Assert BetterV raw AIG node-count exact anti-correlation with critical-path depth:
    # At every width W in {8, 16, 32, 64}, AIG nodes strictly order RCA < BKA < SKA < KSA
    # while unit-delay critical-path depth strictly orders RCA > BKA > SKA > KSA!
    for w in (8, 16, 32, 64):
        r, bk, sk, ks = rows[w]["RCA"], rows[w]["BKA"], rows[w]["SKA"], rows[w]["KSA"]
        assert int(r["and_nodes"]) < int(bk["and_nodes"]) < int(sk["and_nodes"]) < int(ks["and_nodes"])
        assert int(r["depth"]) > int(bk["depth"]) > int(sk["depth"]) > int(ks["depth"])

    # Assert Harris (2003) (levels, fanout, wire-span) physical trade-off cube at W = 64:
    # - Sklansky (SKA) blows up gate fanout (34 vs 8), making SKA slower than BKA under
    #   capacitive fanout load (43.9 > 42.1) despite 8 fewer logic levels (18 vs 26)!
    # - Kogge-Stone (KSA) matches BKA's unbuffered AIG gate fanout (8 == 8) while blowing
    #   up horizontal wire-span congestion by 7.11x (4095 vs 576 bit-pitches)!
    assert int(rows[64]["SKA"]["max_fanout"]) == 34
    assert int(rows[64]["KSA"]["max_fanout"]) == int(rows[64]["BKA"]["max_fanout"]) == 8
    assert float(rows[64]["BKA"]["fo_delay"]) < float(rows[64]["SKA"]["fo_delay"])
    assert int(rows[64]["KSA"]["wire_span"]) == 4095 and int(rows[64]["BKA"]["wire_span"]) == 576

    print(
        f"  Priority-encoder AST sensitivity: raw `aigmap`={raw_mux_stats['and_nodes']} nodes "
        f"vs `strash`={strash_mux_stats['and_nodes']} nodes (depth={strash_mux_stats['depth']})"
    )
    for w in (8, 16, 32, 64):
        r, bk, sk, ks = rows[w]["RCA"], rows[w]["BKA"], rows[w]["SKA"], rows[w]["KSA"]
        speedup = int(r["depth"]) / int(ks["depth"])
        node_overhead = (int(ks["and_nodes"]) / int(r["and_nodes"]) - 1.0) * 100.0
        print(
            f"  W={w:2d}: RCA=({r['and_nodes']:3d}n,d={r['depth']:3d}) | "
            f"BKA=({bk['and_nodes']:3d}n,d={bk['depth']:2d},fo={bk['max_fanout']:2d},foD={bk['fo_delay']:4.1f},span={bk['wire_span']:4d}) | "
            f"SKA=({sk['and_nodes']:3d}n,d={sk['depth']:2d},fo={sk['max_fanout']:2d},foD={sk['fo_delay']:4.1f}) | "
            f"KSA=({ks['and_nodes']:4d}n,d={ks['depth']:2d},fo={ks['max_fanout']:2d},span={ks['wire_span']:4d}) "
            f"[KSA +{node_overhead:.1f}%n, {speedup:.2f}x depth]"
        )


# ============================================================================
# Pillar 5: Finite Random-Vector Escape vs Bit-Exact Combinational Miter (CEC)
# ============================================================================


def decode_input_index(idx: int, w: int) -> tuple[int, int, int]:
    mask = (1 << w) - 1
    a = idx & mask
    b = (idx >> w) & mask
    cin = (idx >> (2 * w)) & 1
    return a, b, cin


def build_ksa_bounded_stages(
    aig: AIG, a: list[int], b: list[int], cin: int, max_stages: int
) -> list[int]:
    """Kogge-Stone adder limited to `max_stages` prefix doublings (models the classic
    floor(log2(W)) vs ceil(log2(W)) off-by-one stage-count bug on non-power-of-2 W)."""
    w = len(a)
    p0 = [aig.xor_(ai, bi) for ai, bi in zip(a, b)]
    g0 = [aig.and_(ai, bi) for ai, bi in zip(a, b)]
    g = list(g0)
    p = list(p0)
    g[0] = aig.or_(g0[0], aig.and_(p0[0], cin))
    p[0] = aig.const0()

    stride = 1
    stages = 0
    while stride < w and stages < max_stages:
        ng = list(g)
        np = list(p)
        for i in range(stride, w):
            ng[i] = aig.or_(g[i], aig.and_(p[i], g[i - stride]))
            np[i] = aig.and_(p[i], p[i - stride])
        g, p = ng, np
        stride <<= 1
        stages += 1

    carries = [cin] + g[: w - 1]
    sums = [aig.xor_(p0[i], carries[i]) for i in range(w)]
    sums.append(g[w - 1])
    return sums


def build_split_rca(
    aig: AIG, a: list[int], b: list[int], cin: int, cut_bit: int
) -> list[int]:
    """Speculative carry-cut RCA that drops `p_{cut-1} & c_{cut-1}` at `cut_bit`,
    breaking the O(W) critical path into two shorter parallel chains."""
    c = cin
    sums: list[int] = []
    for idx, (ai, bi) in enumerate(zip(a, b)):
        p = aig.xor_(ai, bi)
        g = aig.and_(ai, bi)
        sums.append(aig.xor_(p, c))
        if idx + 1 == cut_bit:
            c = g  # Drops propagate chain across cut_bit!
        else:
            c = aig.or_(g, aig.and_(p, c))
    sums.append(c)
    return sums


def run_probe_5() -> None:
    print("========================================================================")
    print("PROBE 5: Finite-Testbench PPA Reward Hacking vs Exact Combinational Miter")
    print("Provenance: [exhaustive 2^21-input bit-parallel AIG miter + deterministic random-suite simulation]")

    # Exhaustive bit-parallel AIG combinational miter at W = 10 (2^21 = 2,097,152 inputs!)
    w = 10
    masks10, n10 = make_exhaustive_adder_masks(w)

    candidates: list[tuple[str, Callable[[AIG, list[int], list[int], int], list[int]]]] = [
        ("Exact_RCA10 (ref)", build_rca),
        ("Exact_KSA10 (ceil=4)", lambda g, a, b, c: build_ksa_bounded_stages(g, a, b, c, 4)),
        ("Buggy_KSA10 (floor=3)", lambda g, a, b, c: build_ksa_bounded_stages(g, a, b, c, 3)),
        ("Buggy_SplitRCA10(c=6)", lambda g, a, b, c: build_split_rca(g, a, b, c, 6)),
        (
            "Buggy_ConstWire_pe",
            lambda g, a, _b, _c: [g.const0() for _ in range(len(a) + 1)],
        ),
    ]

    gold_aig = AIG(strash=True)
    gold_pis = [gold_aig.pi() for _ in range(2 * w + 1)]
    gold_lits = build_rca(gold_aig, gold_pis[:w], gold_pis[w : 2 * w], gold_pis[2 * w])
    gold_stats = gold_aig.stats(gold_lits)
    gold_adp = int(gold_stats["and_nodes"]) * int(gold_stats["depth"])
    gold_tt = gold_aig.eval_bitparallel(masks10, gold_lits, n10)

    # 50 independent 100-vector random RTLLM suites + small-integer directed suite (a, b < 64)
    rng = random.Random(20260603)
    suites_100 = [[rng.randrange(n10) for _ in range(100)] for _ in range(50)]
    small_int_suite = [
        (a | (b << w) | (cin << (2 * w)))
        for a in range(0, 64, 9)
        for b in range(0, 64, 9)
        for cin in (0, 1)
    ]

    sim_only_best: tuple[float, str, int] = (-1.0, "", 0)
    cec_gated_best: tuple[float, str, int] = (-1.0, "", 0)
    cand_metrics: dict[str, dict[str, float | int | tuple[int, int, int] | None]] = {}

    for name, builder in candidates:
        g = AIG(strash=True)
        pis = [g.pi() for _ in range(2 * w + 1)]
        out_lits = builder(g, pis[:w], pis[w : 2 * w], pis[2 * w])
        st = g.stats(out_lits)
        tt = g.eval_bitparallel(masks10, out_lits, n10)

        diff_mask = 0
        for g_m, c_m in zip(gold_tt, tt):
            diff_mask |= g_m ^ c_m
        err_count = diff_mask.bit_count()
        first_cex = (
            decode_input_index((diff_mask & -diff_mask).bit_length() - 1, w)
            if diff_mask
            else None
        )

        suites_passed = sum(
            1 for suite in suites_100 if all(((diff_mask >> idx) & 1) == 0 for idx in suite)
        )
        small_int_pass = all(((diff_mask >> idx) & 1) == 0 for idx in small_int_suite)

        if name == "Buggy_ConstWire_pe":
            print(
                f"  {name:22s}: nodes={st['and_nodes']:3d}, depth={st['depth']:2d} (0-ps delay floor!), "
                f"CEC_mismatches={err_count:7d}/{n10} ({err_count / n10 * 100:5.2f}%), "
                f"1vec_TB_pass_on_pe=True"
            )
            continue

        cand_adp = int(st["and_nodes"]) * int(st["depth"])
        r_sim_suite0 = (
            0.1 + 1.0 + 10.0 * (gold_adp / cand_adp)
            if all(((diff_mask >> idx) & 1) == 0 for idx in suites_100[0])
            else 0.1
        )
        r_cec = (
            0.1 + 1.0 + 10.0 * (gold_adp / cand_adp)
            if err_count == 0
            else 0.1
        )
        p_binom_100 = (1.0 - err_count / n10) ** 100
        emp_pct = suites_passed / 50.0 * 100.0
        cand_metrics[name] = {
            "nodes": int(st["and_nodes"]),
            "depth": int(st["depth"]),
            "adp": cand_adp,
            "err": err_count,
            "suites_passed": suites_passed,
            "first_cex": first_cex,
        }

        print(
            f"  {name:22s}: nodes={st['and_nodes']:3d}, depth={st['depth']:2d}, "
            f"CEC_err={err_count:4d}/{n10} ({err_count / n10 * 100:5.3f}%), "
            f"100vec_pass={suites_passed:2d}/50 ({emp_pct:4.1f}%, theory {p_binom_100 * 100:4.1f}%), "
            f"small_int_pass={small_int_pass}, r_sim={r_sim_suite0:5.2f}, r_cec={r_cec:5.2f}"
            + (f", min_cex={first_cex}" if first_cex else "")
        )

        if r_sim_suite0 > sim_only_best[0]:
            sim_only_best = (r_sim_suite0, name, err_count)
        if r_cec > cec_gated_best[0]:
            cec_gated_best = (r_cec, name, err_count)

    # Assert non-vacuous quantitative invariants:
    # 1. Buggy_KSA10 (floor(log2(10))=3 stages) has strictly fewer AIG nodes (132 < 138) at
    #    equal critical-path depth (12 == 12, ADP 1584 < 1656) relative to Exact_KSA10, passes
    #    100% of small-integer tests and 35/50 (70.0% empirical; 74.6% binomial) 100-vector
    #    random RTLLM suites, and corrupts 6,144 / 2,097,152 inputs (min witness (511, 1, 0)).
    ex_ksa = cand_metrics["Exact_KSA10 (ceil=4)"]
    bg_ksa = cand_metrics["Buggy_KSA10 (floor=3)"]
    assert int(bg_ksa["nodes"]) == 132 and int(ex_ksa["nodes"]) == 138
    assert int(bg_ksa["depth"]) == 12 and int(ex_ksa["depth"]) == 12
    assert int(bg_ksa["adp"]) == 1584 and int(ex_ksa["adp"]) == 1656
    assert int(bg_ksa["err"]) == 6144 and bg_ksa["first_cex"] == (511, 1, 0)
    assert int(bg_ksa["suites_passed"]) == 35
    assert sim_only_best[1] in ("Buggy_KSA10 (floor=3)", "Buggy_SplitRCA10(c=6)")
    assert sim_only_best[2] > 0
    # 2. Exact 2^21-input Combinational Equivalence Checking rejects 100% of buggy candidates
    #    and selects Exact_KSA10 (ceil=4) with 0/2,097,152 errors!
    assert cec_gated_best[1] == "Exact_KSA10 (ceil=4)" and cec_gated_best[2] == 0

    print(
        f"  Sim-only PPA winner: {sim_only_best[1]} (r={sim_only_best[0]:.2f}, {sim_only_best[2]} silent input bugs!) "
        f"vs CEC-gated winner: {cec_gated_best[1]} (r={cec_gated_best[0]:.2f}, {cec_gated_best[2]} bugs)"
    )


def main() -> None:
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    run_probe_5()
    print("========================================================================")
    print("ALL 5 HARDWARE RTL VERIFICATION & PPA PROBES PASSED DETERMINISTICALLY.")


if __name__ == "__main__":
    main()
