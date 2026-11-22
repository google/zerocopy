#!/usr/bin/env python3
"""
Deterministic 5-pillar verification probe for agentic performance engineering,
GPU kernel/compiler autotuning, Roofline diagnosis, and microbenchmark rigor.

Constraints:
- Pure Python 3.10+ standard library only (zero third-party packages).
- Zero disk writes, zero network calls, zero stderr output.
- Bit-identical stdout across PYTHONHASHSEED values.
- Wall-clock target: < 2.0s under `python3 -I -B`.
- Explicit provenance tags and non-vacuous assertions on every sub-probe.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
import random
import statistics
from typing import Callable, Sequence


# =============================================================================
# Probe 1: Behavioral Verifier-Control-Flow Model & fast_p Inflation
# =============================================================================

@dataclass
class SimTensor:
    """Minimal tensor model tracking physical storage, mutability, and laziness."""

    storage: list[float]
    lazy_thunk: Callable[[], list[float]] | None = None

    def is_concrete(self) -> bool:
        return self.lazy_thunk is None and len(self.storage) > 0

    def materialize(self) -> list[float]:
        if self.lazy_thunk is not None:
            return self.lazy_thunk()
        return self.storage

    def clone(self) -> "SimTensor":
        return SimTensor(storage=list(self.materialize()), lazy_thunk=None)

    def zero_(self) -> None:
        for i in range(len(self.storage)):
            self.storage[i] = 0.0


class SimCachingAllocator:
    """Behavioral model of a caching allocator retaining freed physical buffers."""

    def __init__(self) -> None:
        self.freed_buffers: list[list[float]] = []

    def alloc_zeros(self, n: int) -> SimTensor:
        return SimTensor(storage=[0.0] * n)

    def alloc_empty(self, n: int) -> SimTensor:
        for idx, buf in enumerate(self.freed_buffers):
            if len(buf) == n:
                return SimTensor(storage=self.freed_buffers.pop(idx))
        return SimTensor(storage=[0.0] * n)

    def free(self, t: SimTensor, poison: bool = False) -> None:
        if t.lazy_thunk is None and len(t.storage) > 0:
            buf = list(t.storage)
            if poison:
                buf = [math.nan] * len(buf)
            self.freed_buffers.append(buf)


@dataclass
class KernelExecSpec:
    name: str
    true_speedup: float
    is_adversarial: bool
    requires_python_nn_module: bool
    fn: Callable[[list[SimTensor], SimCachingAllocator, dict[str, float]], SimTensor]


def _allclose(a: Sequence[float], b: Sequence[float], atol: float, rtol: float) -> bool:
    if len(a) != len(b):
        return False
    for x, y in zip(a, b):
        if math.isnan(x) or math.isnan(y):
            return False
        if abs(x - y) > atol + rtol * abs(y):
            return False
    return True


def _ref_compute(inputs: list[SimTensor], scale: float) -> list[float]:
    a = inputs[0].materialize()
    b = inputs[1].materialize()
    return [scale * (x * y + 0.25 * x) for x, y in zip(a, b)]


def _make_kernel_classes(scale: float, base_time_ms: float = 10.0) -> list[KernelExecSpec]:
    def k_legit(inputs, alloc, timing):
        out = SimTensor(storage=_ref_compute(inputs, scale))
        timing["default_ms"] = base_time_ms / 1.35
        timing["aux_ms"] = 0.0
        return out

    def k_alloc_reuse(inputs, alloc, timing):
        # Pattern documented in KernelBench result_reuse_kernel.py L8:
        # torch::empty() recycles freed reference output memory across or within trials.
        out = alloc.alloc_empty(len(inputs[0].storage))
        timing["default_ms"] = base_time_ms / 80.0
        timing["aux_ms"] = 0.0
        return out

    def k_zero_out(inputs, alloc, timing):
        # Pattern documented in KernelBench zero_out_kernel.py:
        # mutates inputs in place (A.zero_(); B.zero_()) and returns zeros.
        for t in inputs:
            t.zero_()
        out = alloc.alloc_zeros(len(inputs[0].storage))
        timing["default_ms"] = base_time_ms / 60.0
        timing["aux_ms"] = 0.0
        return out

    def k_async_9_5x(inputs, alloc, timing):
        # Non-blocking CUDA stream calibrated below excessive_speedup_threshold=10.
        out = SimTensor(storage=_ref_compute(inputs, scale))
        timing["default_ms"] = base_time_ms / 9.5
        timing["aux_ms"] = base_time_ms - timing["default_ms"]
        return out

    def k_async_25x(inputs, alloc, timing):
        # Pattern from KernelBench non_default_stream_kernel.py:
        # launches work on cudaStreamNonBlocking outside default-stream events.
        out = SimTensor(storage=_ref_compute(inputs, scale))
        timing["default_ms"] = base_time_ms / 25.0
        timing["aux_ms"] = base_time_ms - timing["default_ms"]
        return out

    def k_lazy_40x(inputs, alloc, timing):
        # Pattern from CUDA-L1 (arXiv:2507.14111v13) LazyMatmul(torch.Tensor):
        # Python subclass returning empty storage during timing and computing on read.
        snap = [t.clone() for t in inputs]
        out = SimTensor(storage=[], lazy_thunk=lambda: _ref_compute(snap, scale))
        timing["default_ms"] = base_time_ms / 40.0
        timing["aux_ms"] = 0.0
        return out

    def k_low_snr_zero(inputs, alloc, timing):
        # Returns zeros on a task with small reference output magnitude.
        out = alloc.alloc_zeros(len(inputs[0].storage))
        timing["default_ms"] = base_time_ms / 50.0
        timing["aux_ms"] = 0.0
        return out

    return [
        KernelExecSpec("legitimate_1.35x", 1.35, False, False, k_legit),
        KernelExecSpec("alloc_reuse_80x", 0.0, True, False, k_alloc_reuse),
        KernelExecSpec("zero_out_inputs_60x", 0.0, True, False, k_zero_out),
        KernelExecSpec("async_stream_9.5x", 1.0, True, False, k_async_9_5x),
        KernelExecSpec("async_stream_25x", 1.0, True, False, k_async_25x),
        KernelExecSpec("lazy_tensor_40x", 1.0, True, True, k_lazy_40x),
        KernelExecSpec("low_snr_zero_50x", 0.0, True, False, k_low_snr_zero),
    ]


@dataclass
class HarnessPolicy:
    name: str
    order: str                     # "ref_first_freed", "ref_first_live", "cuda_first"
    clone_inputs: bool
    poison_freed: bool
    tol: float
    device_wide_sync: bool
    check_materialized: bool
    offline_snr_floor: float       # Dataset curation check on unmodified ref output
    accepts_python_nn_module: bool # False for compiled C++/CUDA .cu loaders (robust-kbench)
    reject_excessive_gt: float | None


def eval_under_harness(
    spec: KernelExecSpec,
    harness: HarnessPolicy,
    scale: float,
    base_time_ms: float = 10.0,
) -> tuple[bool, float, bool, str]:
    """Returns (accepted_correct, reported_speedup, warning_flag, status_note)."""
    if spec.requires_python_nn_module and not harness.accepts_python_nn_module:
        # robust-kbench@078f5bab cuda_correct.py L39-46 loads a compiled .cu extension
        # via torch.utils.cpp_extension.load(...).forward; bare Python nn.Module
        # LazyMatmul subclasses do not apply without C++/pybind11 wrapping.
        return False, 0.0, False, "N/A(.cu)"

    rng = random.Random(101)
    raw_inputs = [
        SimTensor([rng.uniform(0.5, 1.5) for _ in range(16)]),
        SimTensor([rng.uniform(0.5, 1.5) for _ in range(16)]),
    ]
    clean_ref_vals = _ref_compute([t.clone() for t in raw_inputs], scale)
    if harness.offline_snr_floor > 0.0 and max(abs(x) for x in clean_ref_vals) < harness.offline_snr_floor:
        return False, 0.0, False, "BLK(SNR)"

    alloc = SimCachingAllocator()
    timing: dict[str, float] = {"default_ms": base_time_ms, "aux_ms": 0.0}

    def prep_inputs() -> list[SimTensor]:
        return [t.clone() for t in raw_inputs] if harness.clone_inputs else raw_inputs

    if harness.order == "ref_first_freed":
        # Models freed-reference / cross-trial allocator recycling (result_reuse_kernel.py L8).
        ref_vals = _ref_compute(prep_inputs(), scale)
        ref_t = SimTensor(storage=list(ref_vals))
        alloc.free(ref_t, poison=harness.poison_freed)
        cand_t = spec.fn(prep_inputs(), alloc, timing)
        cand_vals = cand_t.materialize()
    elif harness.order == "ref_first_live":
        # KernelBench@423217d9 eval.py L777-783 (and 7dd9cfa L590-595): ref stays live.
        ref_t = SimTensor(storage=_ref_compute(prep_inputs(), scale))
        cand_t = spec.fn(prep_inputs(), alloc, timing)
        ref_vals = ref_t.materialize()
        cand_vals = cand_t.materialize()
    elif harness.order == "cuda_first":
        # robust-kbench@078f5bab correct_forward_fn.py L47-55: cuda -> ref -> cuda2.
        cand_t = spec.fn(prep_inputs(), alloc, timing)
        ref_t = SimTensor(storage=_ref_compute(prep_inputs(), scale))
        cand_t2 = spec.fn(prep_inputs(), alloc, timing)
        ref_vals = ref_t.materialize()
        cand_vals = cand_t.materialize()
        cand_vals2 = cand_t2.materialize()
        if not _allclose(ref_vals, cand_vals2, harness.tol, harness.tol):
            return False, 0.0, False, "BLK"
    else:
        raise ValueError(harness.order)

    if harness.check_materialized and not cand_t.is_concrete():
        return False, 0.0, False, "BLK"

    if not _allclose(cand_vals, ref_vals, harness.tol, harness.tol):
        return False, 0.0, False, "BLK"

    measured_ms = (timing["default_ms"] + timing["aux_ms"]) if harness.device_wide_sync else timing["default_ms"]
    speedup = base_time_ms / max(measured_ms, 1e-9)
    warning = speedup > 10.0
    if harness.reject_excessive_gt is not None and speedup > harness.reject_excessive_gt:
        return False, 0.0, warning, "BLK"
    return True, speedup, warning, "OK"


def _exploit_succeeded(spec: KernelExecSpec, ok: bool, spd: float) -> bool:
    if not ok:
        return False
    return spec.true_speedup == 0.0 or spd > spec.true_speedup + 0.05


def run_probe_1() -> None:
    print("========================================================================")
    print("PROBE 1: Behavioral Verifier-Control-Flow Model & fast_p Inflation")
    print("Provenance: [behavioral model of pinned repository control flow] + [controlled simulation]")
    print("========================================================================")

    harnesses = [
        HarnessPolicy(
            "Freed-ref + KB-v0 tol (freed-ref, tol=1e-2, def-stream)",
            "ref_first_freed", False, False, 1e-2, False, False, 0.0, True, None,
        ),
        HarnessPolicy(
            "KB-main@423217d9 (ref-live, tol=1e-4, def-stream, warn)",
            "ref_first_live", False, False, 1e-4, False, False, 0.0, True, None,
        ),
        HarnessPolicy(
            "robust-kbench@078f5bab (.cu, cuda->ref UNCLONED, def-str)",
            "cuda_first", False, True, 1e-5, False, False, 0.01, False, None,
        ),
        HarnessPolicy(
            "CUDA-L1-patch (KB ref-live, tol=1e-4, dev-sync, lazy-chk)",
            "ref_first_live", False, False, 1e-4, True, True, 0.0, True, None,
        ),
        HarnessPolicy(
            "Counterfactual (cuda->ref UNCLONED + dev-sync + lazy-chk)",
            "cuda_first", False, True, 1e-4, True, True, 0.01, True, None,
        ),
        HarnessPolicy(
            "Full-Hardened (cloned+poison+dev-sync+lazy+SNR=0.01)",
            "cuda_first", True, True, 1e-5, True, True, 0.01, True, None,
        ),
    ]

    normal_specs = _make_kernel_classes(scale=1.0)
    low_snr_specs = _make_kernel_classes(scale=0.002)
    sub_tol_specs = _make_kernel_classes(scale=3e-5)

    results_by_harness: dict[str, dict[str, tuple[bool, float, bool, str]]] = {}
    for h in harnesses:
        res: dict[str, tuple[bool, float, bool, str]] = {}
        for sp_n, sp_l in zip(normal_specs, low_snr_specs):
            use_scale = 0.002 if sp_n.name == "low_snr_zero_50x" else 1.0
            sp = sp_l if sp_n.name == "low_snr_zero_50x" else sp_n
            res[sp.name] = eval_under_harness(sp, h, scale=use_scale)
        results_by_harness[h.name] = res

    print("Exploit Success Matrix (pure-Python behavioral control-flow model; no GPU execution):")
    for h in harnesses:
        r = results_by_harness[h.name]
        bypasses = sum(
            1 for sp in normal_specs if sp.is_adversarial and _exploit_succeeded(sp, r[sp.name][0], r[sp.name][1])
        )
        legit_ok, legit_sp, _, _ = r["legitimate_1.35x"]
        assert legit_ok and abs(legit_sp - 1.35) < 1e-9
        tags = []
        for sp in normal_specs:
            if not sp.is_adversarial:
                continue
            ok, spd, warn, note = r[sp.name]
            short = sp.name.split("_")[0] + "_" + sp.name.split("_")[1]
            if not ok:
                tags.append(f"{short}:{note}")
            elif _exploit_succeeded(sp, ok, spd):
                w = "!W" if warn else ""
                tags.append(f"{short}:{spd:.1f}x{w}")
            else:
                tags.append(f"{short}:NEUT({spd:.1f}x)")
        print(f"  {h.name:58s} | exploit={bypasses}/6 | " + ", ".join(tags))

    # Sub-tol (scale=3e-5, max|ref| ~ 7.9e-5 < 1e-4) SNR hygiene check:
    # Even with dev-sync + lazy-chk + tol=1e-4 (CUDA-L1-patch), missing offline SNR filter
    # allows zero-output shortcut on near-zero tasks; robust-kbench & Full-Hardened block it.
    sub_tol_zero = [sp for sp in sub_tol_specs if sp.name == "low_snr_zero_50x"][0]
    c1_sub_ok, c1_sub_sp, _, _ = eval_under_harness(sub_tol_zero, harnesses[3], scale=3e-5)
    rk_sub_ok, _, _, rk_sub_note = eval_under_harness(sub_tol_zero, harnesses[2], scale=3e-5)
    hd_sub_ok, _, _, hd_sub_note = eval_under_harness(sub_tol_zero, harnesses[5], scale=3e-5)
    print(
        f"  Sub-tol SNR check (max|ref|~7.9e-5): CUDA-L1-patch(no SNR floor)={c1_sub_sp:.1f}x "
        f"| robust-kbench={rk_sub_note} | Full-Hardened={hd_sub_note}"
    )
    assert c1_sub_ok is True and abs(c1_sub_sp - 50.0) < 1e-9
    assert rk_sub_ok is False and hd_sub_ok is False

    r_v0 = results_by_harness[harnesses[0].name]
    r_kb = results_by_harness[harnesses[1].name]
    r_rk = results_by_harness[harnesses[2].name]
    r_c1 = results_by_harness[harnesses[3].name]
    r_cf = results_by_harness[harnesses[4].name]
    r_hd = results_by_harness[harnesses[5].name]

    assert r_v0["alloc_reuse_80x"][0] is True
    assert r_v0["low_snr_zero_50x"][0] is True
    assert r_kb["zero_out_inputs_60x"][0] is False
    assert r_kb["async_stream_9.5x"][0] is True and r_kb["async_stream_9.5x"][2] is False
    assert r_kb["async_stream_25x"][0] is True and r_kb["async_stream_25x"][2] is True
    assert r_kb["lazy_tensor_40x"][0] is True

    # robust-kbench@078f5bab: 3/6 direct pure-CUDA exploits; Python LazyMatmul is N/A(.cu).
    assert r_rk["alloc_reuse_80x"][0] is False
    assert r_rk["zero_out_inputs_60x"][0] is True
    assert r_rk["async_stream_9.5x"][0] is True
    assert r_rk["async_stream_25x"][0] is True
    assert r_rk["lazy_tensor_40x"][0] is False and r_rk["lazy_tensor_40x"][3] == "N/A(.cu)"
    assert sum(1 for sp in normal_specs if sp.is_adversarial and _exploit_succeeded(sp, r_rk[sp.name][0], r_rk[sp.name][1])) == 3

    # CUDA-L1 patch on KB ref-live neutralizes streams and blocks Python LazyMatmul.
    assert r_c1["async_stream_25x"][1] == 1.0
    assert r_c1["lazy_tensor_40x"][0] is False
    assert r_c1["zero_out_inputs_60x"][0] is False

    # Counterfactual cuda->ref UNCLONED still reopens zero_out_inputs even with dev-sync + lazy-chk.
    assert r_cf["zero_out_inputs_60x"][0] is True
    assert r_cf["lazy_tensor_40x"][0] is False
    assert r_cf["async_stream_25x"][1] == 1.0

    for sp in normal_specs:
        if sp.is_adversarial:
            ok, spd, _, _ = r_hd[sp.name]
            if "async_stream" in sp.name:
                assert ok is True and abs(spd - 1.0) < 1e-9
            else:
                assert ok is False, f"Full-Hardened must reject {sp.name}"

    # 100-task pool fast_p inflation under behavioral control-flow model.
    print("\n100-Task Pool fast_p Inflation (True fast_1 = 0.200, True fast_5 = 0.000):")
    pool = (
        [("legit_fast", 1.35)] * 20
        + [("legit_slow", 0.75)] * 60
        + [("zero_out_inputs_60x", 0.0)] * 5
        + [("async_stream_9.5x", 1.0)] * 5
        + [("async_stream_25x", 1.0)] * 5
        + [("lazy_tensor_40x", 1.0)] * 5
    )
    for h in [harnesses[1], harnesses[2], harnesses[3], harnesses[4], harnesses[5]]:
        r = results_by_harness[h.name]
        f1 = 0
        f5 = 0
        spd_sum = 0.0
        for kind, _ in pool:
            if kind == "legit_fast":
                ok, s = True, 1.35
            elif kind == "legit_slow":
                ok, s = True, 0.75
            else:
                ok, s, _, _ = r[kind]
            if ok and s > 1.0:
                f1 += 1
            if ok and s > 5.0:
                f5 += 1
            spd_sum += s if ok else 0.0
        print(
            f"  {h.name:58s} | fast_1={f1/100:.3f} | fast_5={f5/100:.3f} | mean_reported={spd_sum/100:.2f}x"
        )
        if h.name.startswith("KB-main"):
            assert f1 == 35 and f5 == 15
        if h.name.startswith("robust-kbench"):
            assert f1 == 35 and f5 == 15  # 20 legit + 5 zero_out + 10 async_stream (.cu blocks lazy)
        if h.name.startswith("Full-Hardened"):
            assert f1 == 20 and f5 == 0


# =============================================================================
# Probe 2: Williams (2009) Roofline Futility & Telemetry Mechanism Illustration
# =============================================================================

@dataclass(frozen=True)
class RooflineArch:
    name: str
    peak_gflops: float
    bw_gbs: float

    @property
    def ridge_point(self) -> float:
        return self.peak_gflops / self.bw_gbs

    def attainable(self, intensity: float, peak_scale: float = 1.0, bw_scale: float = 1.0) -> float:
        return min(self.peak_gflops * peak_scale, self.bw_gbs * bw_scale * intensity)


def run_probe_2() -> None:
    print("\n========================================================================")
    print("PROBE 2: Williams (2009) Roofline Optimization Futility & Telemetry Noise")
    print("Provenance: [exact calculation on published equations] + [illustrative mechanism simulation]")
    print("========================================================================")

    archs = [
        RooflineArch("Xeon Clovertown e5345 (Stream)", 75.0, 5.9),
        RooflineArch("Opteron X4 Barcelona (Stream)", 74.0, 16.6),
        RooflineArch("Sun Niagara 2 T2+ (Stream)", 19.0, 26.0),
        RooflineArch("IBM Cell QS20 SPEs (Stream)", 29.0, 47.0),
        RooflineArch("NVIDIA L40S (FP32)", 91600.0, 864.0),
        RooflineArch("NVIDIA H100 SXM5 (FP16 TC)", 989000.0, 3350.0),
    ]
    print("Part 2A [exact calculation on published equations] -- Ridge Points I* = P_peak / B_peak:")
    for a in archs:
        print(f"  {a.name:32s}: P={a.peak_gflops:9.1f} GFLOP/s | B={a.bw_gbs:6.1f} GB/s | I*={a.ridge_point:6.2f} FLOP/B")

    assert abs(archs[0].ridge_point - 75.0 / 5.9) < 1e-9
    assert abs(archs[1].ridge_point - 74.0 / 16.6) < 1e-9
    assert abs(archs[2].ridge_point - 19.0 / 26.0) < 1e-9
    assert abs(archs[3].ridge_point - 29.0 / 47.0) < 1e-9

    h100 = archs[-1]
    i0 = 15.0
    p_base = h100.attainable(i0, peak_scale=0.25, bw_scale=0.80)
    p_compute_4x = h100.attainable(i0, peak_scale=1.00, bw_scale=0.80)
    sp_compute = p_compute_4x / p_base
    p_fusion_4x = h100.attainable(i0 * 4.0, peak_scale=0.25, bw_scale=0.80)
    sp_fusion = p_fusion_4x / p_base
    p_fusion_20x_no_tc = h100.attainable(i0 * 20.0, peak_scale=0.25, bw_scale=0.80)
    p_fusion_20x_plus_tc = h100.attainable(i0 * 20.0, peak_scale=1.00, bw_scale=0.80)

    print(
        f"\n  H100 Unfused Kernel (I={i0:.1f} < I*={h100.ridge_point:.1f}): "
        f"4x compute opt -> {sp_compute:.3f}x speedup (0.0% gain); "
        f"4x traffic fusion -> {sp_fusion:.3f}x speedup"
    )
    print(
        f"  Post-Fusion Phase Transition (I=300 > I*): "
        f"fusion-only={p_fusion_20x_no_tc/p_base:.2f}x; "
        f"fusion+compute(4x)={p_fusion_20x_plus_tc/p_base:.2f}x"
    )
    assert abs(sp_compute - 1.0) < 1e-12
    assert abs(sp_fusion - 4.0) < 1e-12
    assert p_fusion_20x_plus_tc > 3.0 * p_fusion_20x_no_tc

    # Part 2B: Parameterized mechanism illustration (ordering is by construction of action-bias
    # and edit-hazard parameters; illustrates how counter-induced action misallocation under
    # I < I* interacts with Roofline ceilings to explain KernelPro's empirical inversion).
    print("\nPart 2B [illustrative mechanism simulation -- parameterized] -- 100-Task Multi-Turn (T=8):")
    rng = random.Random(2026)
    tasks = []
    for _ in range(100):
        intensity_ratio = rng.uniform(0.08, 0.70) if rng.random() < 0.70 else rng.uniform(1.10, 3.00)
        tasks.append((intensity_ratio, 0.30, 0.55))

    def sim_policy(policy: str, seed: int) -> tuple[float, float, float]:
        prng = random.Random(seed)
        speedups: list[float] = []
        for i_ratio, p_eff0, b_eff0 in tasks:
            base_perf = min(p_eff0, b_eff0 * i_ratio)
            cur_i, cur_p, cur_b = i_ratio, p_eff0, b_eff0
            best_sp = 1.0
            for _ in range(8):
                mem_bound = (cur_b * cur_i) < cur_p
                if policy == "roofline_surrogate":
                    choose_mem = mem_bound if prng.random() < 0.95 else (not mem_bound)
                    bug_prob = 0.08
                elif policy == "no_feedback":
                    choose_mem = prng.random() < 0.60
                    bug_prob = 0.14
                elif policy == "raw_ncu_dump":
                    choose_mem = prng.random() < 0.28
                    bug_prob = 0.28
                else:
                    raise ValueError(policy)

                if prng.random() < bug_prob:
                    continue

                cand_i, cand_p, cand_b = cur_i, cur_p, cur_b
                if choose_mem:
                    cand_i = min(cur_i * prng.uniform(1.18, 1.45), 3.5)
                    cand_b = min(cur_b * prng.uniform(1.06, 1.18), 0.92)
                else:
                    cand_p = min(cur_p * prng.uniform(1.25, 1.55), 0.95)

                sp = min(cand_p, cand_b * cand_i) / base_perf
                if sp > best_sp:
                    best_sp = sp
                    cur_i, cur_p, cur_b = cand_i, cand_p, cand_b
            speedups.append(best_sp)

        geo = math.exp(sum(math.log(s) for s in speedups) / len(speedups))
        fast1 = sum(1 for s in speedups if s > 1.05) / len(speedups)
        fast2 = sum(1 for s in speedups if s > 2.00) / len(speedups)
        return geo, fast1, fast2

    res_no = sim_policy("no_feedback", 11)
    res_raw = sim_policy("raw_ncu_dump", 12)
    res_rf = sim_policy("roofline_surrogate", 13)

    for lbl, (geo, f1, f2) in [
        ("No Feedback (p_mem=0.60, bug=0.14)", res_no),
        ("Raw NCU Bias (p_mem=0.28, bug=0.28)", res_raw),
        ("Roofline (acc=0.95, bug=0.08)", res_rf),
    ]:
        print(f"  {lbl:36s} | geomean={geo:.2f}x | fast_1.05={f1*100:5.1f}% | fast_2={f2*100:5.1f}%")

    assert res_rf[0] > res_no[0] > res_raw[0]
    assert res_rf[2] > res_no[2] > res_raw[2]


# =============================================================================
# Probe 3: Hierarchical Layout Bias, Repo Gates & Evolutionary max_k Curse
# =============================================================================

def _normal_sf(z: float) -> float:
    return 0.5 * math.erfc(z / math.sqrt(2.0))


def _percentile_linear(sorted_xs: Sequence[float], q: float) -> float:
    n = len(sorted_xs)
    pos = q * (n - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return sorted_xs[lo]
    return sorted_xs[lo] + (pos - lo) * (sorted_xs[hi] - sorted_xs[lo])


def swe_perf_filter_outliers(data: Sequence[float], threshold: float = 1.5) -> list[float]:
    """Exact reproduction of SWE-Perf@9e8fed28 evaluation/utils.py L345-361.
    Reproduces the live implementation ignoring `threshold` and hardcoding 1 * iqr.
    """
    _ = threshold
    s = sorted(data)
    q1 = _percentile_linear(s, 0.25)
    q3 = _percentile_linear(s, 0.75)
    iqr = q3 - q1
    lo = q1 - 1.0 * iqr
    hi = q3 + 1.0 * iqr
    return [x for x in data if lo <= x <= hi]


def mann_whitney_u_pvalue(x: Sequence[float], y: Sequence[float], alternative: str) -> float:
    """Pure-stdlib Mann-Whitney U test with tie correction and continuity correction."""
    nx, ny = len(x), len(y)
    if nx == 0 or ny == 0:
        return 1.0
    combined = [(v, 0) for v in x] + [(v, 1) for v in y]
    combined.sort(key=lambda t: t[0])
    n = nx + ny
    ranks_x = 0.0
    tie_term = 0.0
    i = 0
    while i < n:
        j = i
        while j < n and combined[j][0] == combined[i][0]:
            j += 1
        avg_rank = 0.5 * (i + 1 + j)
        cnt = j - i
        if cnt > 1:
            tie_term += cnt * cnt * cnt - cnt
        for k in range(i, j):
            if combined[k][1] == 0:
                ranks_x += avg_rank
        i = j
    u_x = ranks_x - nx * (nx + 1) / 2.0
    mean_u = nx * ny / 2.0
    var_u = (nx * ny / 12.0) * ((n + 1) - tie_term / (n * (n - 1))) if n > 1 else 0.0
    if var_u <= 0.0:
        return 1.0
    sd_u = math.sqrt(var_u)
    if alternative == "greater":
        z = (u_x - mean_u - 0.5) / sd_u
        return _normal_sf(z)
    if alternative == "two-sided":
        z = (abs(u_x - mean_u) - 0.5) / sd_u
        return min(1.0, 2.0 * _normal_sf(max(0.0, z)))
    raise ValueError(alternative)


def swe_perf_max_sig_improvement(
    cand: Sequence[float],
    base: Sequence[float],
    p_threshold: float = 0.10,
    step: float = 0.001,
    max_increase: float = 1.0,
) -> float:
    """Exact reproduction of SWE-Perf@9e8fed28 evaluation/utils.py L365-398."""
    x = 0.0
    last_sig = 0.0
    while x <= max_increase:
        adj_b = [b * (1.0 - x) for b in base]
        if mann_whitney_u_pvalue(adj_b, cand, "greater") < p_threshold:
            last_sig = x
            x += step
        else:
            break
    return last_sig


def _welch_t(x: Sequence[float], y: Sequence[float]) -> float:
    """Exact reproduction of bheisler/criterion.rs@3dbc6c61 sample.rs L171-180."""
    nx, ny = len(x), len(y)
    sx = 0.0
    sx2 = 0.0
    for v in x:
        sx += v
        sx2 += v * v
    sy = 0.0
    sy2 = 0.0
    for v in y:
        sy += v
        sy2 += v * v
    mx = sx / nx
    my = sy / ny
    vx = max(0.0, (sx2 - sx * mx) / (nx - 1))
    vy = max(0.0, (sy2 - sy * my) / (ny - 1))
    den = math.sqrt(vx / nx + vy / ny)
    return 0.0 if den == 0.0 else (mx - my) / den


def criterion_dual_gate(
    cand: Sequence[float],
    base: Sequence[float],
    rng: random.Random,
    nresamples: int = 200,
    alpha: float = 0.05,
    noise_threshold: float = 0.01,
) -> bool:
    """Faithful scaled-resample reproduction of bheisler/criterion.rs@3dbc6c61:
    - Mixed bootstrap Welch t (src/analysis/compare.rs L82)
    - Exact two-tailed Distribution::p_value = 2 * min(hits, n - hits) / n
      where hits = count(x < obs_t) (src/stats/mod.rs L63-75, src/analysis/mod.rs L200)
    - Dual gate: p < alpha AND 95% relative-mean CI strictly below -noise_threshold
      (src/report.rs L602, L788-794).
    Note: Criterion defaults are sample_size=100, nresamples=100_000 (src/lib.rs L411-412);
    scaled here to n=20, nresamples=200 for <2.0s pure-stdlib runtime.
    """
    nx, ny = len(cand), len(base)
    obs_t = _welch_t(cand, base)
    pooled = list(cand) + list(base)
    pooled_sq = [v * v for v in pooled]
    n_tot = len(pooled)
    rnd = rng.random
    inv_nx = 1.0 / nx
    inv_ny = 1.0 / ny
    inv_nx1 = 1.0 / (nx - 1)
    inv_ny1 = 1.0 / (ny - 1)
    sqrt = math.sqrt
    _int = int

    hits = 0
    for _ in range(nresamples):
        sx = 0.0
        sx2 = 0.0
        for _i in range(nx):
            idx = _int(rnd() * n_tot)
            sx += pooled[idx]
            sx2 += pooled_sq[idx]
        sy = 0.0
        sy2 = 0.0
        for _j in range(ny):
            idx = _int(rnd() * n_tot)
            sy += pooled[idx]
            sy2 += pooled_sq[idx]
        mx = sx * inv_nx
        my = sy * inv_ny
        vx = (sx2 - sx * mx) * inv_nx1
        vy = (sy2 - sy * my) * inv_ny1
        if vx < 0.0:
            vx = 0.0
        if vy < 0.0:
            vy = 0.0
        den = sqrt(vx * inv_nx + vy * inv_ny)
        t_null = 0.0 if den == 0.0 else (mx - my) / den
        if t_null < obs_t:
            hits += 1

    tails = hits if hits < (nresamples - hits) else (nresamples - hits)
    p_value = (2.0 * tails) / nresamples
    if p_value >= alpha:
        return False

    rel_changes = []
    for _ in range(nresamples):
        sc = 0.0
        for _i in range(nx):
            sc += cand[_int(rnd() * nx)]
        sb = 0.0
        for _j in range(ny):
            sb += base[_int(rnd() * ny)]
        rel_changes.append((sc * inv_nx) / (sb * inv_ny) - 1.0)
    rel_changes.sort()
    lb = _percentile_linear(rel_changes, 0.025)
    ub = _percentile_linear(rel_changes, 0.975)
    return lb < -noise_threshold and ub < -noise_threshold


def _student_t_upper_tail(t_abs: float, df: float) -> float:
    """Accurate pure-stdlib Student-t upper-tail P(T_df >= t_abs) for t_abs >= 0, real df > 0."""
    c = math.gamma(0.5 * (df + 1.0)) / (math.sqrt(df * math.pi) * math.gamma(0.5 * df))
    steps = 24
    a = math.atan(t_abs / math.sqrt(df))
    b = 0.5 * math.pi
    h = (b - a) / steps
    p_exp = df - 1.0
    s = (math.cos(a) ** p_exp) + (math.cos(b) ** p_exp)
    for k in range(1, steps):
        s += (4.0 if k % 2 == 1 else 2.0) * (math.cos(a + k * h) ** p_exp)
    return min(0.5, max(0.0, c * math.sqrt(df) * (h / 3.0) * s))


def _student_t_quantile(upper_tail_prob: float, df: float) -> float:
    """Invert P(T_df >= q) == upper_tail_prob via bisection."""
    lo, hi = 0.0, 20.0
    while _student_t_upper_tail(hi, df) > upper_tail_prob:
        hi *= 2.0
    for _ in range(44):
        mid = 0.5 * (lo + hi)
        if _student_t_upper_tail(mid, df) > upper_tail_prob:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def kalibera_jones_fieller_ratio_test(
    cand_layout_means: Sequence[float],
    base_layout_means: Sequence[float],
) -> tuple[float, float, float]:
    """Kalibera & Jones (ISMM '13 / arXiv:2007.10899v1) Fieller ratio-of-means inference
    for H0: mu_cand / mu_base >= 1 vs H1: mu_cand / mu_base < 1 (candidate faster),
    using top-level layout means with Welch-Satterthwaite degrees of freedom nu_WS.
    Returns (one_sided_p, speedup_point_est, nu_ws).
    """
    r2 = len(cand_layout_means)
    mc = sum(cand_layout_means) / r2
    mb = sum(base_layout_means) / r2
    vc = sum((v - mc) ** 2 for v in cand_layout_means) / (r2 - 1)
    vb = sum((v - mb) ** 2 for v in base_layout_means) / (r2 - 1)
    uc = vc / r2
    ub = vb / r2
    tot_u = uc + ub
    if tot_u <= 0.0:
        return (0.0 if mc < mb else 1.0), (mb / mc if mc > 0 else 1.0), float(2 * (r2 - 1))
    nu_ws = (tot_u * tot_u) / ((uc * uc + ub * ub) / (r2 - 1))
    # Exact Fieller pivot at theta_0 = 1: T(1) = (mb - mc) / sqrt(uc + ub)
    t_stat = (mb - mc) / math.sqrt(tot_u)
    if t_stat >= 0.0:
        p_one = _student_t_upper_tail(t_stat, nu_ws)
    else:
        p_one = 1.0 - _student_t_upper_tail(-t_stat, nu_ws)
    return p_one, mb / mc, nu_ws


def fieller_ratio_ci(
    cand_layout_means: Sequence[float],
    base_layout_means: Sequence[float],
    tail_alpha: float,
) -> tuple[float, float]:
    """Closed-form Fieller confidence bounds for ratio theta = mu_cand / mu_base
    at critical value t_{nu_WS, 1 - tail_alpha}.
    (Pass tail_alpha=alpha/2 for two-sided (1-alpha) CI; tail_alpha=alpha for one-sided upper bound.)
    """
    r2 = len(cand_layout_means)
    mc = sum(cand_layout_means) / r2
    mb = sum(base_layout_means) / r2
    uc = (sum((v - mc) ** 2 for v in cand_layout_means) / (r2 - 1)) / r2
    ub = (sum((v - mb) ** 2 for v in base_layout_means) / (r2 - 1)) / r2
    tot_u = uc + ub
    nu_ws = (tot_u * tot_u) / ((uc * uc + ub * ub) / (r2 - 1))
    t_crit = _student_t_quantile(tail_alpha, nu_ws)
    t2 = t_crit * t_crit
    a_coef = mb * mb - t2 * ub
    b_coef = mc * mb
    c_coef = mc * mc - t2 * uc
    assert a_coef > 0.0, "Fieller denominator must be strictly positive"
    disc = math.sqrt(max(0.0, b_coef * b_coef - a_coef * c_coef))
    return (b_coef - disc) / a_coef, (b_coef + disc) / a_coef


def kalibera_jones_hier_bootstrap_ratio_ci(
    cand_groups: Sequence[Sequence[float]],
    base_groups: Sequence[Sequence[float]],
    rng: random.Random,
    nboot: int = 1000,
    alpha: float = 0.05,
) -> tuple[float, float]:
    """Two-level hierarchical bootstrap CI for ratio mu_cand / mu_base (Kalibera & Jones Sec. 4.1)."""
    r2c = len(cand_groups)
    r2b = len(base_groups)
    r1c = len(cand_groups[0])
    r1b = len(base_groups[0])
    rr = rng.randrange
    ratios = []
    for _ in range(nboot):
        sc = 0.0
        for _g in range(r2c):
            grp = cand_groups[rr(r2c)]
            for _i in range(r1c):
                sc += grp[rr(r1c)]
        sb = 0.0
        for _g in range(r2b):
            grp = base_groups[rr(r2b)]
            for _i in range(r1b):
                sb += grp[rr(r1b)]
        ratios.append((sc / (r2c * r1c)) / (sb / (r2b * r1b)))
    ratios.sort()
    return _percentile_linear(ratios, alpha / 2.0), _percentile_linear(ratios, 1.0 - alpha / 2.0)


def holm_bonferroni_any_reject(p_values: Sequence[float], alpha: float = 0.05) -> bool:
    k = len(p_values)
    for idx, p in enumerate(sorted(p_values)):
        if p < alpha / (k - idx):
            return True
    return False


def run_probe_3() -> None:
    print("\n========================================================================")
    print("PROBE 3: Hierarchical Layout Bias, Repo Gates & Evolutionary max_k Curse")
    print("Provenance: [exact calculation on published equations] + [exact/scaled-resample repo gates] + [controlled simulation]")
    print("========================================================================")

    # Part 3A: Exact Kalibera & Jones ISMM 2013 Eq. (3) Table 5 reproduction.
    print("Part 3A [exact calculation on published equations] -- Kalibera-Jones ISMM '13 Table 5:")
    kj_table5 = [
        ("bloat6", 35.5, 110.0, 14.0, 2.7, 10),
        ("lusearch9", 1.7, 12.3, 3.4, 30.3, 1),
        ("xalan6", 10.8, 24.6, 7.2, 8.9, 2),
        ("xalan9", 6.7, 71.8, 3.5, 0.8, 15),
    ]
    for name, c1, c2, t1, t2, expected_r1 in kj_table5:
        r1_star = math.ceil(math.sqrt((c2 * (t1 ** 2)) / (c1 * (t2 ** 2))))
        print(f"  {name:10s}: c1={c1:4.1f}s c2={c2:5.1f}s t1={t1:4.1f}% t2={t2:4.1f}% -> r1*={r1_star:2d} (Table 5: {expected_r1})")
        assert r1_star == expected_r1
    # Verify bloat6 t1=14.1% rounding yields the identical integer r1*=10.
    assert math.ceil(math.sqrt((110.0 * (14.1 ** 2)) / (35.5 * (2.7 ** 2)))) == 10

    # Part 3B: Repository gate audit under synthetic right-skewed null H0 (true speedup = 1.000x).
    rng = random.Random(314159)

    def gen_runs(layout_sigma: float, iter_sigma: float, r2: int, r1: int) -> list[list[float]]:
        out = []
        for _ in range(r2):
            layout_mult = math.exp(rng.gauss(0.0, layout_sigma)) if layout_sigma > 0 else 1.0
            runs = [100.0 * layout_mult * (0.85 + 0.15 * math.exp(rng.gauss(0.0, iter_sigma / 0.15))) for _ in range(r1)]
            out.append(runs)
        return out

    # Regime I: Zero layout bias, within-process right-skewed jitter (sigma_iter=0.04).
    # Fast exact gates evaluated at N=2000; scaled-resample Criterion.rs (nres=200) at N=400.
    n_fast_trials = 2000
    n_crit_trials = 400
    fp_algotune_no_lay = 0
    fp_untrim_mwu10_no_lay = 0
    fp_sweperf_no_lay = 0
    fp_gbench_mwu_no_lay = 0
    fp_criterion_no_lay = 0
    sweperf_trim_fracs = []

    for idx in range(n_fast_trials):
        b20 = gen_runs(0.0, 0.04, 1, 20)[0]
        c20 = gen_runs(0.0, 0.04, 1, 20)[0]
        if min(b20[:10]) / min(c20[:10]) > 1.02:
            fp_algotune_no_lay += 1
        if mann_whitney_u_pvalue([b * 0.999 for b in b20], c20, "greater") < 0.10:
            fp_untrim_mwu10_no_lay += 1
        bf = swe_perf_filter_outliers(b20, threshold=1.5)
        cf = swe_perf_filter_outliers(c20, threshold=1.5)
        sweperf_trim_fracs.append(1.0 - (len(bf) + len(cf)) / 40.0)
        if swe_perf_max_sig_improvement(cf, bf, p_threshold=0.10, step=0.001, max_increase=0.002) > 0.0:
            fp_sweperf_no_lay += 1
        if statistics.median(c20) < statistics.median(b20) and mann_whitney_u_pvalue(b20, c20, "two-sided") < 0.05:
            fp_gbench_mwu_no_lay += 1
        if idx < n_crit_trials:
            if criterion_dual_gate(c20, b20, rng, nresamples=200, alpha=0.05, noise_threshold=0.01):
                fp_criterion_no_lay += 1

    full_shift = swe_perf_max_sig_improvement([85.0 + 0.1 * i for i in range(20)], [100.0 + 0.1 * i for i in range(20)])
    assert 0.140 <= full_shift <= 0.155

    fpr_at_0 = fp_algotune_no_lay / n_fast_trials
    fpr_ut10_0 = fp_untrim_mwu10_no_lay / n_fast_trials
    fpr_sp_0 = fp_sweperf_no_lay / n_fast_trials
    fpr_gb_0 = fp_gbench_mwu_no_lay / n_fast_trials
    fpr_cr_0 = fp_criterion_no_lay / n_crit_trials
    mean_trim = sum(sweperf_trim_fracs) / len(sweperf_trim_fracs)

    print("\nPart 3B [exact/scaled-resample repo gates + controlled simulation] -- Null FPR (H0: true=1.000x):")
    print(f"  Regime I (sigma_layout=0.00, sigma_iter=0.04, N={n_fast_trials}; Criterion N={n_crit_trials}, nres=200 vs 100k default):")
    print(f"    AlgoTune min-of-10 (>1.02x):                  FPR = {fpr_at_0*100:5.1f}%")
    print(f"    Untrimmed 1-sided MWU (p<0.10, x=0.001):      FPR = {fpr_ut10_0*100:5.1f}% (control)")
    print(f"    SWE-Perf 1.0xIQR + 1-sided MWU (p<0.10):      FPR = {fpr_sp_0*100:5.1f}% (trimmed {mean_trim*100:.1f}% -> inflates FPR above 10%!)")
    print(f"    google/benchmark untrimmed MWU (p<0.05, dir): FPR = {fpr_gb_0*100:5.1f}%")
    print(f"    Criterion.rs exact-p dual gate (p<0.05 & >1%):FPR = {fpr_cr_0*100:5.1f}%")

    # Regime II: Cross-layout bias (Mytkowicz/Stabilizer sigma_layout=0.05, sigma_iter=0.02),
    # K=20 null candidates, aligned SWE-Perf step=0.001 (plus paper delta>0.05 check).
    n_evo_campaigns = 100
    k_cands = 20
    fwer_at_lay = 0
    fwer_sp_001_lay = 0
    fwer_sp_05_lay = 0
    fwer_cr_lay = 0
    fwer_kj_holm = 0
    max_phantom_at: list[float] = []
    max_phantom_kj: list[float] = []

    # Cross-check Fieller ratio CI against Kalibera-Jones two-level hierarchical bootstrap.
    demo_base_g = gen_runs(0.05, 0.02, 10, 2)
    demo_cand_g = [[0.92 * x for x in grp] for grp in gen_runs(0.05, 0.02, 10, 2)]
    demo_bm = [sum(g) / len(g) for g in demo_base_g]
    demo_cm = [sum(g) / len(g) for g in demo_cand_g]
    fieller_95 = fieller_ratio_ci(demo_cm, demo_bm, tail_alpha=0.025)
    hboot_95 = kalibera_jones_hier_bootstrap_ratio_ci(demo_cand_g, demo_base_g, rng, nboot=1000, alpha=0.05)
    demo_p1, _, _ = kalibera_jones_fieller_ratio_test(demo_cm, demo_bm)
    _, fieller_one_hi = fieller_ratio_ci(demo_cm, demo_bm, tail_alpha=0.05)
    # Exact algebraic equivalence: one-sided Fieller upper bound < 1.0 iff p_one < 0.05
    assert (fieller_one_hi < 1.0) == (demo_p1 < 0.05)
    assert abs(fieller_95[0] - hboot_95[0]) < 0.035 and abs(fieller_95[1] - hboot_95[1]) < 0.035

    for _ in range(n_evo_campaigns):
        base_1l = gen_runs(0.05, 0.02, 1, 20)[0]
        base_1l_min10 = min(base_1l[:10])
        base_1l_filt = swe_perf_filter_outliers(base_1l)

        hit_at = False
        hit_sp_001 = False
        hit_sp_05 = False
        hit_cr = False
        best_sp_at = 1.0

        base_kj_means = [sum(r) / len(r) for r in gen_runs(0.05, 0.02, 10, 2)]
        kj_pvals: list[float] = []
        best_sp_kj = 1.0

        for _c in range(k_cands):
            cand_1l = gen_runs(0.05, 0.02, 1, 20)[0]
            sp_at = base_1l_min10 / min(cand_1l[:10])
            if sp_at > best_sp_at:
                best_sp_at = sp_at
            if sp_at > 1.05:
                hit_at = True
            if (not hit_sp_001) or (not hit_sp_05):
                cand_1l_filt = swe_perf_filter_outliers(cand_1l)
                if not hit_sp_001:
                    if swe_perf_max_sig_improvement(cand_1l_filt, base_1l_filt, p_threshold=0.10, step=0.001, max_increase=0.002) > 0.0:
                        hit_sp_001 = True
                if not hit_sp_05:
                    if mann_whitney_u_pvalue([b * 0.95 for b in base_1l_filt], cand_1l_filt, "greater") < 0.10:
                        hit_sp_05 = True
            if not hit_cr:
                if criterion_dual_gate(cand_1l, base_1l, rng, nresamples=200, alpha=0.05, noise_threshold=0.01):
                    hit_cr = True

            cand_kj_means = [sum(r) / len(r) for r in gen_runs(0.05, 0.02, 10, 2)]
            p_kj, sp_kj, _ = kalibera_jones_fieller_ratio_test(cand_kj_means, base_kj_means)
            kj_pvals.append(p_kj)
            if sp_kj > best_sp_kj:
                best_sp_kj = sp_kj

        fwer_at_lay += int(hit_at)
        fwer_sp_001_lay += int(hit_sp_001)
        fwer_sp_05_lay += int(hit_sp_05)
        fwer_cr_lay += int(hit_cr)
        fwer_kj_holm += int(holm_bonferroni_any_reject(kj_pvals, alpha=0.05))
        max_phantom_at.append(best_sp_at)
        max_phantom_kj.append(best_sp_kj)

    print(
        f"  Fieller vs. 2-level hierarchical bootstrap check (95% ratio CI, true=0.920): "
        f"Fieller=[{fieller_95[0]:.3f}, {fieller_95[1]:.3f}] vs H-Boot=[{hboot_95[0]:.3f}, {hboot_95[1]:.3f}]"
    )
    print(f"\n  Regime II (Mytkowicz layout bias sigma_layout=0.05, K={k_cands} null candidates, {n_evo_campaigns} campaigns):")
    print(f"    AlgoTune min-of-10 (>1.05x, 1 layout):      FWER = {fwer_at_lay/n_evo_campaigns*100:5.1f}% | mean max_k speedup = {statistics.mean(max_phantom_at):.3f}x")
    print(f"    SWE-Perf 1.0xIQR+MWU (x=0.001, 1 layout):   FWER = {fwer_sp_001_lay/n_evo_campaigns*100:5.1f}% (paper delta>0.05 floor: {fwer_sp_05_lay/n_evo_campaigns*100:5.1f}%)")
    print(f"    Criterion.rs exact-p dual gate (1 layout):  FWER = {fwer_cr_lay/n_evo_campaigns*100:5.1f}%  <-- 1-level gate collapses under layout bias!")
    print(f"    Kalibera-Jones Fieller(r2=10, WS) + Holm:   FWER = {fwer_kj_holm/n_evo_campaigns*100:5.1f}% (1-sided alpha=0.05) | mean max_k = {statistics.mean(max_phantom_kj):.3f}x")

    assert fpr_sp_0 > fpr_ut10_0 + 0.02 and fpr_sp_0 > 0.11
    assert fpr_ut10_0 > fpr_gb_0
    assert mean_trim > 0.05
    assert fpr_cr_0 < 0.04
    assert fwer_cr_lay / n_evo_campaigns > 0.80
    assert fwer_sp_001_lay / n_evo_campaigns > 0.85
    assert fwer_sp_05_lay / n_evo_campaigns > 0.60
    assert fwer_kj_holm / n_evo_campaigns <= 0.09
    assert statistics.mean(max_phantom_at) > 1.08


# =============================================================================
# Probe 4: Aggregate Speedup Metric Distortion, Clamping & Weighting
# =============================================================================

def _arith_mean(xs: Sequence[float]) -> float:
    return sum(xs) / len(xs)


def _geo_mean(xs: Sequence[float]) -> float:
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def _harm_mean(xs: Sequence[float]) -> float:
    return len(xs) / sum(1.0 / x for x in xs)


def run_probe_4() -> None:
    print("\n========================================================================")
    print("PROBE 4: Aggregate Speedup Metric Distortion, Clamping & Weighting")
    print("Provenance: [exact analytical calculation on published scalars] + [controlled simulation]")
    print("========================================================================")

    # Part 4A: Exact analytical sensitivity bounds using ONLY genuinely published
    # robust-kbench (arXiv:2509.14279v1 Sec. 3, App. A.4) scalars (zero fabricated tasks).
    clean_mean_pub = 1.49
    raw_mean_pub = 3.13
    n_l1_l2 = 200
    pub_outliers = [51.159, 123.603]  # Published L1-T12 and L2-T13 speedups
    # Replace 2 of 200 tasks sitting at 1.49x with the 2 published outliers:
    arith_2out = ((n_l1_l2 - 2) * clean_mean_pub + sum(pub_outliers)) / n_l1_l2
    harm_2out = n_l1_l2 / ((n_l1_l2 - 2) / clean_mean_pub + sum(1.0 / x for x in pub_outliers))
    arith_infl_2 = (arith_2out / clean_mean_pub) - 1.0
    harm_infl_2 = (harm_2out / clean_mean_pub) - 1.0
    residual_gap = raw_mean_pub - arith_2out

    print("Part 4A [exact analytical calculation on published scalars] -- robust-kbench (L1+L2, N=200):")
    print(
        f"  Just 2 published outliers (51.159x, 123.603x = 1.0% of N=200) on 1.49x clean base: "
        f"Arith 1.490x -> {arith_2out:.3f}x ({arith_infl_2*100:+.1f}%) | "
        f"Harm 1.490x -> {harm_2out:.3f}x ({harm_infl_2*100:+.1f}%) | "
        f"Remaining gap to 3.13x = +{residual_gap:.3f}x"
    )
    assert arith_infl_2 > 0.55 and harm_infl_2 < 0.015

    # Part 4B: Controlled synthetic lognormal suite (200 tasks rescaled to mean=1.490x) + the 2 published outliers.
    rng = random.Random(404)
    clean_syn = [math.exp(rng.gauss(math.log(1.38), 0.36)) for _ in range(200)]
    scale_factor = 1.490 / _arith_mean(clean_syn)
    clean_syn = [x * scale_factor for x in clean_syn]
    mixed_syn = clean_syn + pub_outliers

    print("Part 4B [controlled simulation -- synthetic suite] -- Adding Only Published 2 Outliers (1.0%):")
    for label, arr in [("Synthetic Clean (200 tasks)", clean_syn), ("+2 Published Outliers (202 tasks)", mixed_syn)]:
        am = _arith_mean(arr)
        gm = _geo_mean(arr)
        hm = _harm_mean(arr)
        med = statistics.median(arr)
        f1 = sum(1 for x in arr if x > 1.0) / len(arr)
        print(f"  {label:35s} | Arith={am:5.2f}x | Geo={gm:5.2f}x | Harm={hm:5.2f}x | Med={med:5.2f}x | fast_1={f1*100:5.1f}%")

    am_infl = (_arith_mean(mixed_syn) / _arith_mean(clean_syn)) - 1.0
    gm_infl = (_geo_mean(mixed_syn) / _geo_mean(clean_syn)) - 1.0
    hm_infl = (_harm_mean(mixed_syn) / _harm_mean(clean_syn)) - 1.0
    print(f"  Synthetic 1% Outlier Shift: Arith={am_infl*100:+.1f}% | Geo={gm_infl*100:+.1f}% | Harm={hm_infl*100:+.1f}%")
    assert am_infl > 0.55 and hm_infl < 0.02

    # Part 4C: Synthetic regression-clamping & Smith (1988) baseline-time weighting demonstrations.
    unclamped = [1.50] * 40 + [1.05] * 25 + [0.50] * 35
    clamped_to_1 = [max(1.0, x) for x in unclamped]
    hm_unclamped = _harm_mean(unclamped)
    hm_clamped = _harm_mean(clamped_to_1)
    fast_1_val = sum(1 for x in unclamped if x > 1.0) / len(unclamped)

    # Smith (1988): unweighted harmonic mean assumes equal baseline work/time per task.
    # Task A: 100ms -> 50ms (2.0x); Task B: 10ms -> 20ms (0.5x).
    base_times = [100.0, 10.0]
    new_times = [50.0, 20.0]
    task_speedups = [b / n for b, n in zip(base_times, new_times)]
    unweighted_hm = _harm_mean(task_speedups)
    weighted_hm = sum(base_times) / sum(new_times)  # exact baseline-time-weighted harmonic mean
    geo_var = _geo_mean(task_speedups)

    print("Part 4C [controlled synthetic illustration on exact mean formulas]:")
    print(
        f"  Clamping 35% 0.50x regressions to 1.0x: Unclamped Harm={hm_unclamped:.3f}x (SLOWDOWN) vs "
        f"Clamped Harm={hm_clamped:.3f}x (APPARENT GAIN) | fast_1={fast_1_val*100:.1f}%"
    )
    print(
        f"  Variable-baseline weighting (100->50ms, 10->20ms): True total-time ratio (weighted Harm)={weighted_hm:.3f}x "
        f"vs Unweighted Harm={unweighted_hm:.3f}x (misclassifies!) | Geo={geo_var:.3f}x"
    )
    assert hm_unclamped < 1.0 < hm_clamped
    assert unweighted_hm < 1.0 < weighted_hm


# =============================================================================
# Probe 5: Schedule-vs-Algorithm Factoring & Hazard-Dependent Crossover
# =============================================================================

def run_probe_5() -> None:
    print("\n========================================================================")
    print("PROBE 5: Schedule-vs-Algorithm Factoring & Hazard-Dependent Crossover")
    print("Provenance: [exact calculation on published ECCO Table 3 data] + [derived analytical model] + [controlled simulation]")
    print("========================================================================")

    # Part 5A: Exact single-step retention / hazard ratios from ECCO (arXiv:2407.14044v2 Table 3,
    # single-step history-editing refinement; no unestablished multi-turn assumption).
    gpt4o_pre, gpt4o_nl, gpt4o_ex, gpt4o_nlex = 0.666, 0.478, 0.608, 0.588
    gpt4o_sp_pre, gpt4o_sp_nl, gpt4o_sp_ex, gpt4o_sp_nlex = 1.64, 2.72, 2.19, 2.39
    cg_pre, cg_nl, cg_ex = 0.425, 0.151, 0.332

    h_gpt_nl = 1.0 - (gpt4o_nl / gpt4o_pre)
    h_gpt_ex = 1.0 - (gpt4o_ex / gpt4o_pre)
    h_cg_nl = 1.0 - (cg_nl / cg_pre)
    h_cg_ex = 1.0 - (cg_ex / cg_pre)

    # Joint expected valid speedup (zero credit for broken output): pass@1 * conditional speedup.
    ev_pre = gpt4o_pre * gpt4o_sp_pre
    ev_nl = gpt4o_nl * gpt4o_sp_nl
    ev_ex = gpt4o_ex * gpt4o_sp_ex
    ev_nlex = gpt4o_nlex * gpt4o_sp_nlex

    print("Part 5A [exact calculation on published ECCO Table 3 data + derived analytical bound]:")
    print(
        f"  ECCO GPT-4o 1-step hazard (1 - post/pre): NL self-refine={h_gpt_nl*100:5.2f}% (-18.8 pp) "
        f"vs Exec-refine={h_gpt_ex*100:5.2f}% (-5.8 pp) -> {h_gpt_nl/h_gpt_ex:.2f}x lower hazard"
    )
    print(
        f"  ECCO CodeGemma 1-step hazard:             NL self-refine={h_cg_nl*100:5.2f}% (-27.4 pp) "
        f"vs Exec-refine={h_cg_ex*100:5.2f}% (-9.3 pp) -> {h_cg_nl/h_cg_ex:.2f}x lower hazard"
    )
    print(
        f"  ECCO GPT-4o pass@1*speedup (0x if broken): pre={ev_pre:.3f}x | NL={ev_nl:.3f}x | "
        f"Exec={ev_ex:.3f}x | NL+Exec={ev_nlex:.3f}x"
    )
    # Closed-form 1-step analytical break-even headroom R* = 1 / (1 - p_leak):
    r_star_05 = 1.0 / (1.0 - 0.05)
    r_star_12 = 1.0 / (1.0 - 0.12)
    r_star_25 = 1.0 / (1.0 - 0.25)
    print(
        f"  Analytical 1-step break-even R*(p_leak) = 1/(1-p_leak): "
        f"p_leak=0.05 -> {r_star_05:.3f} | p_leak=0.12 -> {r_star_12:.3f} | p_leak=0.25 -> {r_star_25:.3f}"
    )
    assert h_gpt_nl > 3.0 * h_gpt_ex
    assert h_cg_nl > 2.5 * h_cg_ex
    assert ev_nlex > ev_ex > ev_nl > ev_pre
    assert r_star_25 > r_star_12 > r_star_05 > 1.0

    # Part 5B: Controlled multi-turn (T=10) sensitivity simulation showing crossover depends on
    # empirical hidden-test leakage p_leak (no universal numeric R* threshold).
    print("\nPart 5B [controlled simulation] -- Multi-Turn (T=10) Crossover Sensitivity Across p_leak:")
    s_sched = 1.60
    t_turns = 10
    n_sim = 500
    headrooms = [1.0, 1.25, 1.5, 2.0, 3.0]
    first_exec_win_by_leak: dict[float, float] = {}

    for p_leak in [0.08, 0.28]:
        print(f"  Hidden-test algorithmic leakage p_leak = {p_leak:.2f}:")
        first_win = None
        for r_headroom in headrooms:
            s_algo = s_sched * r_headroom
            rng = random.Random(int(5000 + p_leak * 1000 + r_headroom * 100))
            eff_sched = 0.0
            eff_exec = 0.0
            eff_nl = 0.0
            ok_nl_cnt = 0

            for _ in range(n_sim):
                # 1. Factored schedule-only (correctness by construction, p_bug == 0)
                best_sc = 1.0
                for _ in range(t_turns):
                    cand = 1.0 + (s_sched - 1.0) * rng.uniform(0.35, 1.00)
                    if cand > best_sc:
                        best_sc = cand
                eff_sched += best_sc

                # 2. Exec-gated algorithmic rewrite (rollback on public failure;
                #    valid_ex resets to True whenever a semantics-preserving schedule tweak wins).
                best_ex = 1.0
                valid_ex = True
                for _ in range(t_turns):
                    if rng.random() < 0.35:
                        continue
                    if rng.random() < 0.14:
                        cand = s_algo * rng.uniform(0.75, 1.00)
                        if cand > best_ex:
                            best_ex = cand
                            valid_ex = rng.random() > p_leak
                    else:
                        cand = 1.0 + (s_sched - 1.0) * rng.uniform(0.25, 0.90)
                        if cand > best_ex:
                            best_ex = cand
                            valid_ex = True
                eff_exec += best_ex if valid_ex else 0.0

                # 3. Unconstrained NL self-refine (no execution rollback)
                alive = True
                cur_nl = 1.0
                for _ in range(t_turns):
                    if rng.random() < 0.14:
                        alive = False
                    if alive:
                        if rng.random() < 0.14:
                            cur_nl = max(cur_nl, s_algo * rng.uniform(0.75, 1.00))
                        else:
                            cur_nl = max(cur_nl, 1.0 + (s_sched - 1.0) * rng.uniform(0.25, 0.90))
                if alive:
                    ok_nl_cnt += 1
                    eff_nl += cur_nl

            m_sc = eff_sched / n_sim
            m_ex = eff_exec / n_sim
            m_nl = eff_nl / n_sim
            winner = "Schedule-Only" if m_sc >= m_ex else "Exec-Gated-Algo"
            if winner == "Exec-Gated-Algo" and first_win is None:
                first_win = r_headroom
            print(
                f"    R={r_headroom:4.2f} (S_algo={s_algo:4.2f}x) | "
                f"Sched={m_sc:4.2f}x | Exec-Algo={m_ex:4.2f}x | NL-Only={m_nl:4.2f}x (ok={ok_nl_cnt/n_sim*100:4.1f}%) | Winner={winner}"
            )
            assert m_ex > m_nl and m_sc > m_nl
            if r_headroom == 1.0:
                assert m_sc > m_ex
            if r_headroom == 3.0:
                assert m_ex > m_sc
        assert first_win is not None
        first_exec_win_by_leak[p_leak] = first_win

    assert first_exec_win_by_leak[0.28] > first_exec_win_by_leak[0.08], (
        "Higher hidden-test leakage must shift crossover R* upward (no universal constant)"
    )


def main() -> None:
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    run_probe_5()
    print("\nALL 5 PILLAR PROBES PASSED ALL NON-VACUOUS ASSERTIONS.")


if __name__ == "__main__":
    main()
