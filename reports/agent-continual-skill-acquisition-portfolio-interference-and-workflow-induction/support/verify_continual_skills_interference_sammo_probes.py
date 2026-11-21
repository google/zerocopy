#!/usr/bin/env python3
"""Deterministic verification probes for continual skill acquisition, toolbox
pruning, cross-skill portfolio interference, workflow/memory extraction bugs,
instruction-conflict resolution, negation polarity regimes, and structure-
preserving skill optimization.

Evidence-Role Banners:
  - Probe 1A: [exact reproduction of pinned repo logic] (zorazrw/TroVE@c4d16b6a2e)
  - Probe 1B: [toy model / mechanistic surrogate] (equal-retrieval topk=10 ablation)
  - Probe 2A: [derived 3-parameter fit to 3 published endpoints] (Guo et al. 2026)
  - Probe 2B: [toy model / mechanistic surrogate] (symmetric finite-|D_sel| evolution)
  - Probe 3:  [exact reproduction of pinned source bugs] (dynamic-cheatsheet@5cfe3c37e8,
              ExpeL@e41ec9a248, How-Self-Evolution-Reshapes-Skills@db2cdbde29,
              microsoft/sammo@736552381d Rewrite.mutate AST behavior)
  - Probe 4A: [exact analytical / derived calculation] (ConInstruct, DUET, WhoWins)
  - Probe 4B: [exact analytical / derived calculation] + [toy model / illustrative mechanism]
              (Semantic Gravity Wells 2601.08070v1 & Guardrails Beat Guidance 2604.11088v2)

Python 3.10+ stdlib-only. Fixed seed = 20261121. Zero network calls.
Zero wall-clock timestamps in stdout (bit-identical deterministic SHA-256).
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import itertools
import math
import random
import re

SEED = 20261121


def det_seed(tag: str) -> int:
    """Process-independent deterministic seed offset (immune to python3 -I hash randomization)."""
    return int(hashlib.sha256(tag.encode("utf-8")).hexdigest()[:8], 16)


def fast_u01(step_idx: int, fam_id: int, tool_id: int) -> float:
    """Deterministic 32-bit integer mixer in [0, 1] for reproducible query-tool similarity."""
    x = (step_idx * 0x9E3779B1 ^ fam_id * 0x85EBCA77 ^ tool_id * 0xC2B2AE3D ^ SEED) & 0xFFFFFFFF
    x = (((x >> 16) ^ x) * 0x045D9F3B) & 0xFFFFFFFF
    x = ((x >> 16) ^ x) & 0xFFFFFFFF
    return x / 0xFFFFFFFF


# =============================================================================
# PROBE 1: TroVE@c4d16b6a2e Pruning Threshold, topk=10 Specialist Starvation,
#          and parse_library_functions Multi-Import Scope
# =============================================================================


def trove_format_toolbox_pinned(
    toolbox: dict[str, dict[str, object]], topk: int = 10
) -> list[str]:
    """Exact reproduction of zorazrw/TroVE@c4d16b6a2e utils/code.py:312-321.

    Returns the ordered list of visible tool names placed into the IMPORT prompt.
    """
    name_freq_list = [(name, int(d["frequency"])) for name, d in toolbox.items()]
    name_freq_list = sorted(name_freq_list, key=lambda x: -x[1])
    return [tool_name for tool_name, _ in name_freq_list[:topk]]


def trove_trim_library_pinned(
    n: int, library: dict[str, dict[str, object]], trimmed_indices: set[int]
) -> dict[str, dict[str, object]]:
    """Exact reproduction of zorazrw/TroVE@c4d16b6a2e run_trove.py:175-188."""
    threshold = math.log(n, 20)
    for _, d in library.items():
        if int(d["frequency"]) < threshold:
            for idx in d["indices"]:  # type: ignore[attr-defined]
                trimmed_indices.add(int(idx))
    return {name: d for name, d in library.items() if int(d["frequency"]) >= threshold}


def trove_parse_library_functions_pinned(code: str) -> list[dict[str, str]]:
    """Exact reproduction of zorazrw/TroVE@c4d16b6a2e utils/code.py:127-199."""
    assert "\n" not in code
    if "," in code:
        if code.startswith("import"):  # "import math, random"
            sidx = code.index("import") + 6
            lib_list = code[sidx:].strip().split(",")
            lib_list = [lib.strip() for lib in lib_list if lib.strip() != ""]
            tool_dict_list = []
            for lib in lib_list:
                eidx = lib.index(" as") if " as" in lib else len(lib)
                tool_dict = {
                    "name": lib[:eidx].strip(),
                    "docstr": code.strip(),
                    "signature": code.strip(),
                    "function": code.strip(),
                    "type": "import",
                }
                tool_dict_list.append(tool_dict)
                return tool_dict_list  # BUG at utils/code.py:149 (indented inside loop!)
        elif code.startswith("from"):  # "from sympy import solve, symbols"
            assert "import" in code
            sidx = code.index("import")
            library = code[5:sidx].strip()
            func_list = code[sidx + 6 :].strip().split(",")
            func_list = [func.strip() for func in func_list if func.strip() != ""]
            return [
                {
                    "name": f"{library}.{func}",
                    "docstr": f"from {library} import {func}",
                    "signature": f"from {library} import {func}",
                    "function": f"from {library} import {func}",
                    "type": "import",
                }
                for func in func_list
            ]
        return []
    if code.startswith("import"):
        sidx = code.index("import") + 6
        eidx = code.index(" as", sidx) if " as" in code[sidx:] else len(code)
        lib_func = code[sidx:eidx].strip()
        return [
            {
                "name": lib_func,
                "docstr": code.strip(),
                "signature": code.strip(),
                "function": code.strip(),
                "type": "import",
            }
        ]
    if code.startswith("from"):
        sidx = code.index("import")
        library = code[5:sidx].strip()
        func = code[sidx + 6 :].strip()
        return [
            {
                "name": f"{library}.{func}",
                "docstr": code.strip(),
                "signature": code.strip(),
                "function": code.strip(),
                "type": "import",
            }
        ]
    return []


def retrieve_semantic_topk10(
    library: dict[str, dict[str, object]],
    fam: str,
    q_dom: str,
    fam_id: int,
    step_idx: int,
    topk: int = 10,
) -> list[str]:
    """Equal-footed noisy lexical/semantic retriever shared identically across all semantic policies.

    No policy gets an exclusive noiseless sim=1.0 oracle or private usage-rate boost:
    matching-family tools average 0.72, same-domain distractors (including spurious one-offs)
    average 0.54, cross-domain tools average 0.15, plus uniform [-0.25, +0.25] surface noise.
    """
    if len(library) <= topk:
        return list(library.keys())
    scored: list[tuple[float, str]] = []
    for name, d in library.items():
        noise = (fast_u01(step_idx, fam_id, int(d["tid"])) - 0.5) * 0.50  # type: ignore[arg-type]
        if d["family"] == fam:
            base = 0.72
        elif d["domain"] == q_dom:
            base = 0.54
        else:
            base = 0.15
        scored.append((base + noise, name))
    scored.sort(reverse=True)
    return [nm for _, nm in scored[:topk]]


def run_probe_1() -> None:
    print("=" * 78)
    print("PROBE 1: TroVE@c4d16b6a2e Pruning Base, topk=10 Specialist Starvation & Parser")
    print("  1A Banner: [exact reproduction of pinned repo logic]")
    print("  1B Banner: [toy model / mechanistic surrogate] (equal-retrieval 4-way ablation)")
    print("=" * 78)

    # --- Part 1A: Exact repo logic checks ---
    parsed_bare = trove_parse_library_functions_pinned("import math, numpy, sympy")
    parsed_from = trove_parse_library_functions_pinned("from toolbox import find_mean, find_std")
    assert [d["name"] for d in parsed_bare] == ["math"], "Expected early return on bare import"
    assert [d["name"] for d in parsed_from] == [
        "toolbox.find_mean",
        "toolbox.find_std",
    ], "from ... import a, b uses list comprehension and does not hit line 149"

    ratio = math.log(10.0) / (0.5 * math.log(20.0))
    assert abs(ratio - 1.53724357) < 1e-6
    lam_paper_1000 = 0.5 * math.log10(1000)
    lam_code_1000 = math.log(1000, 20)
    assert abs(lam_paper_1000 - 1.5) < 1e-12
    assert 2.0 < lam_code_1000 < 3.0  # 2.305865 -> evicts freq==2 tools!

    pinned_lib: dict[str, dict[str, object]] = {
        f"core_tool_{k}": {"frequency": 5, "indices": [k]} for k in range(10)
    }
    specialist_names = [f"spec_tool_{m}" for m in range(6)]
    visibility_hits = 0
    for step_idx, sname in enumerate(specialist_names, start=100):
        pinned_lib[sname] = {"frequency": 1, "indices": [step_idx]}
        for _ in range(15):
            visible = trove_format_toolbox_pinned(pinned_lib, topk=10)
            if sname in visible:
                visibility_hits += 1
                pinned_lib[sname]["frequency"] = int(pinned_lib[sname]["frequency"]) + 1
    trimmed_idx: set[int] = set()
    surviving_lib = trove_trim_library_pinned(500, pinned_lib, trimmed_idx)
    surviving_specs = [s for s in specialist_names if s in surviving_lib]
    assert visibility_hits == 0
    assert len(surviving_specs) == 0
    assert len(trimmed_idx) == len(specialist_names)

    print(
        f"  [1A] Threshold multiplier log_20(n)/(0.5*log_10(n)) = {ratio:.4f}x (+{(ratio-1)*100:.2f}%)"
    )
    print(
        f"       At n=1000: paper lambda={lam_paper_1000:.3f} (keeps freq>=2) vs "
        f"code lambda={lam_code_1000:.3f} (deletes freq==2)"
    )
    print(
        f"       parse_library_functions: 'import math, numpy, sympy' -> {[d['name'] for d in parsed_bare]} "
        f"(drops 2/3) | 'from toolbox import ...' -> {len(parsed_from)}/2 kept"
    )
    print(
        f"       Exact topk=10 starvation: {visibility_hits}/90 specialist IMPORT prompts saw tool; "
        f"surviving specialists at n=500 trim = {len(surviving_specs)}/{len(specialist_names)} (0.0%)"
    )

    # --- Part 1B: Equal-footed 4-policy streaming simulation (N=2000, topk=10 prompt cap) ---
    # Stream schedule:
    #   - 10 core families arrive across t=0..1999;
    #   - For t>=500 (w.p. 0.35), specialist queries arrive:
    #       * allow_recurring_specialists=True: 6 mid-stream specialists (t>=500) + 6 late-shift
    #         specialists arriving in the final window (t>=1925, age<=75 at t=2000 so each valid
    #         reused tool reaches frequency=2 < log_20(2000)=2.537 but >= log_20(75)=1.441);
    #       * allow_recurring_specialists=False (pure-noise negative control): unique non-recurring
    #         ephemeral tasks arrive and emit spurious oneoff_* tools into `library`!
    def simulate_stream(
        policy: str, allow_recurring_specialists: bool = True
    ) -> tuple[float, int, int, int, int, int]:
        stream_rng = random.Random(SEED)
        act_rng = random.Random(SEED + 7919)
        n_steps = 2000
        core_fams = [f"core_{k}" for k in range(10)]
        early_specs = [f"spec_{k}" for k in range(6)]
        late_specs = [f"spec_{k}" for k in range(6, 12)]
        all_specs = early_specs + late_specs
        fam_to_id = {f: idx + 1 for idx, f in enumerate(core_fams + all_specs)}

        library: dict[str, dict[str, object]] = {}
        correct_count = 0
        spurious_counter = 0
        next_tid = 1

        for t in range(n_steps):
            u_arr = stream_rng.random()
            c_idx = stream_rng.randrange(10)
            e_idx = stream_rng.randrange(6)
            l_idx = stream_rng.randrange(6)
            if t >= 500 and u_arr < 0.35:
                if allow_recurring_specialists:
                    fam = late_specs[l_idx] if t >= 1925 else early_specs[e_idx]
                    fid = fam_to_id[fam]
                else:
                    fam = f"spec_ephemeral_{t}"
                    fid = 10000 + t
                is_specialist = True
            else:
                fam = core_fams[c_idx]
                fid = fam_to_id[fam]
                is_specialist = False
            q_dom = fam.split("_")[0]

            if policy == "pinned_trove":
                visible = trove_format_toolbox_pinned(library, topk=10)
            elif policy in (
                "unpruned_semantic_topk10",
                "global_trim_semantic_topk10",
                "age_trim_semantic_topk10",
            ):
                visible = retrieve_semantic_topk10(library, fam, q_dom, fid, t, topk=10)
            else:
                raise ValueError(policy)

            # Reuse succeeds at 0.90 minus distractor interference; otherwise CREATE/SKIP runs:
            # for recurring families, CREATE synthesizes the reusable family tool at p=0.65
            # (or emits a oneoff_* distractor once |library| >= 10); for ephemeral negative-control
            # tasks, CREATE always emits a spurious oneoff_* tool into `library`.
            valid_tool_name = f"tool_{fam}"
            n_noise_visible = sum(1 for nm in visible if nm.startswith("oneoff_"))
            if valid_tool_name in visible:
                p_hit = max(0.45, 0.90 - 0.035 * n_noise_visible)
                solved = act_rng.random() < p_hit
                library[valid_tool_name]["frequency"] = int(library[valid_tool_name]["frequency"]) + 1
            else:
                base_acc = (0.42 if is_specialist else 0.55) * max(
                    0.30, 1.0 - 0.065 * n_noise_visible
                )
                solved = act_rng.random() < base_acc
                if (not is_specialist) or allow_recurring_specialists:
                    p_synth = 0.80 if (is_specialist and t >= 1925) else 0.65
                    if valid_tool_name not in library and act_rng.random() < p_synth:
                        library[valid_tool_name] = {
                            "tid": next_tid,
                            "frequency": 1,
                            "indices": [t],
                            "born": t,
                            "family": fam,
                            "domain": q_dom,
                        }
                        next_tid += 1
                    elif len(library) >= 10:
                        spurious_counter += 1
                        library[f"oneoff_{spurious_counter}"] = {
                            "tid": next_tid,
                            "frequency": 1,
                            "indices": [t],
                            "born": t,
                            "family": "noise",
                            "domain": q_dom,
                        }
                        next_tid += 1
                else:
                    spurious_counter += 1
                    library[f"oneoff_{spurious_counter}"] = {
                        "tid": next_tid,
                        "frequency": 1,
                        "indices": [t],
                        "born": t,
                        "family": "noise",
                        "domain": "core" if (t % 2 == 0) else "spec",
                    }
                    next_tid += 1
            if solved:
                correct_count += 1

            # Periodic trim every 500 steps (matching run_trove.py default trim_steps=500)
            if (t + 1) % 500 == 0:
                if policy in ("pinned_trove", "global_trim_semantic_topk10"):
                    library = trove_trim_library_pinned(t + 1, library, set())
                elif policy == "age_trim_semantic_topk10":
                    library = {
                        name: d
                        for name, d in library.items()
                        if int(d["frequency"]) >= math.log(max(21, (t + 1) - int(d["born"])), 20)
                    }

        # Final end-of-stream forgetting pass (matching run_trove.py:208)
        if policy in ("pinned_trove", "global_trim_semantic_topk10"):
            library = trove_trim_library_pinned(n_steps, library, set())
        elif policy == "age_trim_semantic_topk10":
            library = {
                name: d
                for name, d in library.items()
                if int(d["frequency"]) >= math.log(max(21, n_steps - int(d["born"])), 20)
            }

        retained_specs = sum(1 for f in all_specs if f"tool_{f}" in library)
        retained_late = sum(1 for f in late_specs if f"tool_{f}" in library)
        retained_noise = sum(1 for nm in library if nm.startswith("oneoff_"))
        return (
            correct_count / n_steps,
            len(library),
            retained_specs,
            retained_late,
            spurious_counter,
            retained_noise,
        )

    acc_unp, sz_unp, sp_unp, _, spur_unp, noise_unp = simulate_stream(
        "unpruned_semantic_topk10", True
    )
    acc_pin, sz_pin, sp_pin, _, _, _ = simulate_stream("pinned_trove", True)
    acc_gbl, sz_gbl, sp_gbl, late_gbl, _, noise_gbl = simulate_stream(
        "global_trim_semantic_topk10", True
    )
    acc_age, sz_age, sp_age, late_age, _, noise_age = simulate_stream(
        "age_trim_semantic_topk10", True
    )
    # Active pure-noise negative control: ephemeral tasks emit >500 oneoff_* tools into library!
    _, sz_neg_age, sp_neg_age, _, spur_neg_age, noise_neg_age = simulate_stream(
        "age_trim_semantic_topk10", False
    )
    _, sz_neg_unp, _, _, spur_neg_unp, noise_neg_unp = simulate_stream(
        "unpruned_semantic_topk10", False
    )

    assert sp_pin == 0 and sz_pin == 10, "Pinned TroVE must starve all post-core specialists"
    assert acc_age >= acc_gbl > acc_unp > acc_pin
    assert late_gbl < late_age == 6, (
        f"Global log_20(n) must evict young freq==2 late specialists ({late_gbl} vs {late_age})"
    )
    assert sp_age == 12 and sz_age == 22 and noise_age == 0 and noise_gbl == 0
    assert spur_neg_age > 500, f"Negative control must actually spawn noise tools: {spur_neg_age}"
    assert sz_neg_age == 10 and sp_neg_age == 0 and noise_neg_age == 0
    assert noise_neg_unp == spur_neg_unp > 500 and sz_neg_unp > 510

    print(
        f"  [1B] Equal-retrieval topk=10 ablation (N=2000): "
        f"Pinned-FreqTopK10 acc={acc_pin*100:.2f}% (lib={sz_pin}, specs={sp_pin}/12) | "
        f"Unpruned-SemTopK10 acc={acc_unp*100:.2f}% (lib={sz_unp}, noise={noise_unp}/{spur_unp})"
    )
    print(
        f"       Trimmed-SemTopK10: Global-log20(n) acc={acc_gbl*100:.2f}% "
        f"(lib={sz_gbl}, specs={sp_gbl}/12, late_specs={late_gbl}/6) | "
        f"Age-log20(age) acc={acc_age*100:.2f}% (lib={sz_age}, specs={sp_age}/12, late_specs={late_age}/6)"
    )
    print(
        f"       Active pure-noise negative control ({spur_neg_age} oneoff_* tools spawned): "
        f"Age-trim final_lib={sz_neg_age} (0/{spur_neg_age} noise leaked) vs "
        f"Unpruned final_lib={sz_neg_unp} ({noise_neg_unp} noise kept)"
    )


# =============================================================================
# PROBE 2: Prior Drift (Guo 2026) Identifiable 3-Parameter Fit & Symmetric MC
# =============================================================================


def fit_mover_stayer_3param(
    k1_obs: float, k30_obs: float, ret_obs: float
) -> tuple[float, float, float]:
    """Solve the exact identifiable 3-parameter mover-stayer Markov model (q_s = 1.0)
    against 3 observed endpoints: K_1 = 1 - L_1, K_30 = 1 - L_30, and R_{1->30} = P(X_30=1 | X_1=0).

    Because stayers survive w.p. q_s = 1.0, P(stayer, X_1 = 0) = 0 identically; thus 100% of items
    lost at Round 1 belong to the mover subpopulation, making Bayes conditional return exact with
    zero unconditioned subpopulation approximation error and zero excess degrees of freedom.
    """

    def eval_k30_for_alpha(alpha: float) -> tuple[float, float, float]:
        p_keep = (k1_obs - alpha) / (1.0 - alpha)
        lo, hi = 0.0, 1.0
        for _ in range(60):
            mid = 0.5 * (lo + hi)
            r = 0.0
            for _ in range(29):
                r = r * p_keep + (1.0 - r) * mid
            if r < ret_obs:
                lo = mid
            else:
                hi = mid
        p_birth = 0.5 * (lo + hi)
        k = 1.0
        for _ in range(30):
            k = k * p_keep + (1.0 - k) * p_birth
        return alpha + (1.0 - alpha) * k, p_keep, p_birth

    lo_a, hi_a = 0.0, min(k1_obs, k30_obs) - 1e-12
    for _ in range(60):
        mid_a = 0.5 * (lo_a + hi_a)
        k30_val, _, _ = eval_k30_for_alpha(mid_a)
        if k30_val < k30_obs:
            lo_a = mid_a
        else:
            hi_a = mid_a
    alpha = 0.5 * (lo_a + hi_a)
    _, p_keep, p_birth = eval_k30_for_alpha(alpha)
    return alpha, p_keep, p_birth


def eval_mover_stayer_exact_bayes(
    alpha: float, p_keep: float, p_birth: float, t: int
) -> tuple[float, float]:
    """Evaluate marginal retention P(X_t=1) and exact Bayes return P(X_t=1 | X_1=0) at q_s = 1.0."""
    q_s = 1.0
    k = 1.0
    for _ in range(t):
        k = k * p_keep + (1.0 - k) * p_birth
    kept_t = alpha * (q_s**t) + (1.0 - alpha) * k
    if t < 1:
        return kept_t, 0.0
    ret_mover = 0.0
    for _ in range(t - 1):
        ret_mover = ret_mover * p_keep + (1.0 - ret_mover) * p_birth
    p_x1_zero_stayer = alpha * (1.0 - q_s)  # 0.0 since q_s == 1.0
    p_x1_zero_mover = (1.0 - alpha) * (1.0 - p_keep)
    bayes_return = (p_x1_zero_stayer * 0.0 + p_x1_zero_mover * ret_mover) / (
        p_x1_zero_stayer + p_x1_zero_mover
    )
    return kept_t, bayes_return


def run_probe_2() -> None:
    print("\n" + "=" * 78)
    print("PROBE 2: Prior Drift (Guo 2026) 3-Parameter Fit & Symmetric Evolution Surrogate")
    print("  2A Banner: [derived 3-parameter fit to 3 published endpoints] (q_s = 1.0)")
    print("  2B Banner: [toy model / mechanistic surrogate] (symmetric per-slot physics)")
    print("=" * 78)

    # --- Part 2A: Exact 3-parameter mover-stayer fit (q_s = 1.0) vs homogeneous decay ---
    r_in_eq = 0.842 ** (1.0 / 30.0)
    r_out_eq = 0.231 ** (1.0 / 30.0)
    gap_30 = (r_in_eq**30 - r_out_eq**30) * 100.0
    assert abs(gap_30 - 61.1) < 1e-6

    homog_sb_r1_loss = 1.0 - (0.187 ** (1.0 / 30.0))
    alpha_out, p_keep_out, p_birth_out = fit_mover_stayer_3param(0.505, 0.187, 0.06)
    alpha_in, p_keep_in, p_birth_in = fit_mover_stayer_3param(0.770, 0.588, 0.30)

    kept_out_1, _ = eval_mover_stayer_exact_bayes(alpha_out, p_keep_out, p_birth_out, 1)
    kept_out_30, ret_out_30 = eval_mover_stayer_exact_bayes(alpha_out, p_keep_out, p_birth_out, 30)
    kept_in_1, _ = eval_mover_stayer_exact_bayes(alpha_in, p_keep_in, p_birth_in, 1)
    kept_in_30, ret_in_30 = eval_mover_stayer_exact_bayes(alpha_in, p_keep_in, p_birth_in, 30)

    assert abs((1.0 - kept_out_1) - 0.495) < 1e-12
    assert abs((1.0 - kept_out_30) - 0.813) < 1e-12
    assert abs(ret_out_30 - 0.06) < 1e-12
    assert abs((1.0 - kept_in_1) - 0.230) < 1e-12
    assert abs((1.0 - kept_in_30) - 0.412) < 1e-12
    assert abs(ret_in_30 - 0.30) < 1e-12

    print(
        f"  [2A] 30-round compound eq. retention: r_in={r_in_eq:.6f}/rd (84.2%) vs "
        f"r_out={r_out_eq:.6f}/rd (23.1%), gap={gap_30:.1f} pp"
    )
    print(
        f"       Non-homogeneous R1 check (SkillsBench 0/10): homogeneous predicts "
        f"{homog_sb_r1_loss*100:.1f}% R1 loss vs actual 49.5%!"
    )
    print(
        f"       Exact 3-param mover-stayer (q_s=1): "
        f"0/10 (alpha={alpha_out:.4f}, p_keep={p_keep_out:.4f}, p_birth={p_birth_out:.4f}) -> "
        f"R1={(1-kept_out_1)*100:.1f}%, R30={(1-kept_out_30)*100:.1f}%, Bayes ret={ret_out_30*100:.2f}% | "
        f">=1/10 (alpha={alpha_in:.4f}, p_keep={p_keep_in:.4f}, p_birth={p_birth_in:.4f}) -> "
        f"Bayes ret={ret_in_30*100:.2f}%"
    )

    # --- Part 2B: Symmetric finite-validation skill evolution Monte Carlo ---
    # Honest finite-sample Bernoulli rollouts on D_sel for ALL modes & ALL n_sel (no oracle shortcut),
    # identical per-touched-slot prior-erasure rate (0.495) across holistic_gated and skillopt_bounded,
    # and zero pre-seeded Step-0 slot immunity!
    def true_ood_pass_rate(
        in_vec: list[int], out_vec: list[int], focus_tag: bool = False
    ) -> float:
        out_w = 0.046 if focus_tag else 0.038
        return min(0.95, 0.40 + 0.008 * sum(in_vec) + out_w * sum(out_vec))

    def run_evolution_mc(mode: str, n_sel: int = 12, prior_erase_bias: bool = True) -> float:
        rng = random.Random(SEED + det_seed(mode) % 10007 + n_sel * 31)
        n_trials = 1000
        steps = 16
        final_scores: list[float] = []
        p_erase_touched = 0.495 if prior_erase_bias else 0.0

        for _ in range(n_trials):
            in_cur = [1] * 10
            out_cur = [1] * 6 + [0] * 4
            if mode == "skilldiff_focus":
                final_scores.append(true_ood_pass_rate(in_cur, out_cur, focus_tag=True))
                continue

            sel_slots = [rng.randrange(10) for _ in range(n_sel)]

            def eval_on_dsel(in_v: list[int], out_v: list[int]) -> float:
                hits = 0
                in_bonus = 0.008 * sum(in_v)
                for sl in sel_slots:
                    p = 0.36 + in_bonus + (0.42 if out_v[sl] == 1 else 0.0)
                    if rng.random() < p:
                        hits += 1
                return hits / n_sel

            cur_val = eval_on_dsel(in_cur, out_cur)
            rejected_bad_slots: set[int] = set()
            stayer_out = [rng.random() < alpha_out for _ in range(10)]
            stayer_in = [rng.random() < alpha_in for _ in range(10)]

            for step in range(steps):
                in_cand = in_cur[:]
                out_cand = out_cur[:]

                if mode == "feedback_free":
                    for j in range(10):
                        if not stayer_in[j]:
                            in_cand[j] = (
                                (1 if rng.random() < p_keep_in else 0)
                                if in_cand[j] == 1
                                else (1 if rng.random() < p_birth_in else 0)
                            )
                        if prior_erase_bias and not stayer_out[j]:
                            out_cand[j] = (
                                (1 if rng.random() < p_keep_out else 0)
                                if out_cand[j] == 1
                                else (1 if rng.random() < p_birth_out else 0)
                            )
                    in_cur, out_cur = in_cand, out_cand
                    continue

                if mode in ("accept_all", "judge_55", "evoguard_98"):
                    if rng.random() < 0.50:
                        zeros = [j for j in range(10) if out_cand[j] == 0]
                        if zeros:
                            out_cand[rng.choice(zeros)] = 1
                    else:
                        ones = [j for j in range(10) if out_cand[j] == 1]
                        for j in rng.sample(ones, k=min(len(ones), 2)):
                            out_cand[j] = 0

                    true_delta = true_ood_pass_rate(in_cand, out_cand) - true_ood_pass_rate(
                        in_cur, out_cur
                    )
                    if mode == "accept_all":
                        accept = True
                    elif mode == "judge_55":
                        cand_in_a = rng.random() < 0.5
                        if abs(true_delta) > 0.06 and rng.random() < 0.35:
                            accept = true_delta > 0
                        else:
                            accept = cand_in_a if rng.random() < 0.72 else (not cand_in_a)
                    else:
                        if true_delta > 0:
                            accept = rng.random() < 0.863
                        elif true_delta < 0:
                            accept = rng.random() < (1.0 - 0.863)
                        else:
                            accept = False
                    if accept:
                        in_cur, out_cur = in_cand, out_cand
                    continue

                # Symmetric edit-locality contrast: ONLY touched-slot count L_t differs!
                if mode == "holistic_gated":
                    touched = list(range(10))
                elif mode == "skillopt_bounded":
                    budget = 2 if step >= steps // 2 else 4
                    cand_slots = [j for j in range(10) if j not in rejected_bad_slots] or list(
                        range(10)
                    )
                    touched = rng.sample(cand_slots, k=min(budget, len(cand_slots)))
                else:
                    raise ValueError(mode)

                touched_zeros = [j for j in touched if out_cur[j] == 0]
                for j in touched:
                    if out_cur[j] == 1 and rng.random() < p_erase_touched:
                        out_cand[j] = 0
                if touched_zeros and rng.random() < 0.65:
                    out_cand[rng.choice(touched_zeros)] = 1

                cand_val = eval_on_dsel(in_cand, out_cand)
                if cand_val > cur_val:
                    in_cur, out_cur = in_cand, out_cand
                    cur_val = cand_val
                elif mode == "skillopt_bounded":
                    for j in touched:
                        if out_cur[j] == 1 and out_cand[j] == 0:
                            rejected_bad_slots.add(j)

            final_scores.append(true_ood_pass_rate(in_cur, out_cur))
        return sum(final_scores) / len(final_scores)

    init_ood = true_ood_pass_rate([1] * 10, [1] * 6 + [0] * 4, focus_tag=False)
    s_ff = run_evolution_mc("feedback_free")
    s_aa = run_evolution_mc("accept_all")
    s_j55 = run_evolution_mc("judge_55")
    s_eg = run_evolution_mc("evoguard_98")
    s_hol_small = run_evolution_mc("holistic_gated", n_sel=8, prior_erase_bias=True)
    s_opt_small = run_evolution_mc("skillopt_bounded", n_sel=8, prior_erase_bias=True)
    s_hol_large = run_evolution_mc("holistic_gated", n_sel=80, prior_erase_bias=True)
    s_opt_large = run_evolution_mc("skillopt_bounded", n_sel=80, prior_erase_bias=True)
    s_diff = run_evolution_mc("skilldiff_focus")
    # Honest finite-sample rollout negative control (no oracle bypass):
    s_hol_ctrl = run_evolution_mc("holistic_gated", n_sel=120, prior_erase_bias=False)

    assert s_ff < init_ood - 0.15, "Feedback-free rewrite must exhibit Prior Drift collapse"
    assert s_hol_small < init_ood, "Holistic rewriter must regress OOD under noisy D_sel=8"
    assert s_opt_small > init_ood and s_opt_large > s_hol_large + 0.05
    assert s_eg > s_j55 > s_aa
    assert s_diff > init_ood
    assert s_hol_ctrl > init_ood + 0.10, "Finite-sample negative control without erasure must climb"

    print(
        f"  [2B] Initial expert skill OOD={init_ood*100:.2f}% | Feedback-free={s_ff*100:.2f}% "
        f"| SkillDiff (insert-only)={s_diff*100:.2f}%"
    )
    print(
        f"       Online single-trace: Accept-All={s_aa*100:.2f}% | 55.6%-Judge={s_j55*100:.2f}% "
        f"| 98.3%-EvoGuard={s_eg*100:.2f}%"
    )
    print(
        f"       Symmetric validation-gated (|D_sel|=8 vs 80, zero Step-0 immunity): "
        f"Holistic(L_t=10)={s_hol_small*100:.2f}% -> {s_hol_large*100:.2f}% | "
        f"Bounded(L_t<=4)={s_opt_small*100:.2f}% -> {s_opt_large*100:.2f}%"
    )
    print(
        f"       Honest finite-rollout negative control (p_erase=0, |D_sel|=120): "
        f"Holistic={s_hol_ctrl*100:.2f}%"
    )


# =============================================================================
# PROBE 3: Exact Pinned Source Bugs (Dynamic Cheatsheet, ExpeL, SkillDiff, SAMMO)
# =============================================================================


def dc_extract_cheatsheet_pinned(response: str, old_cheatsheet: str) -> str:
    """Exact reproduction of suzgunmirac/dynamic-cheatsheet@5cfe3c37e8 extractor.py:62-86."""
    response = response.strip()
    if "<cheatsheet>" in response:
        try:
            txt = response.split("<cheatsheet>")[1].strip()
            txt = txt.split("</cheatsheet>")[0].strip()
            return txt
        except Exception:
            return old_cheatsheet
    else:
        return old_cheatsheet


def dc_extract_cheatsheet_naive_regex(response: str, old_cheatsheet: str) -> str:
    """Naive re.findall(...)[-1] — corrupts when <think> mentions unclosed or example <cheatsheet>."""
    matches = re.findall(r"<cheatsheet>(.*?)</cheatsheet>", response, flags=re.DOTALL)
    if not matches:
        return old_cheatsheet
    candidate = matches[-1].strip()
    return candidate if candidate else old_cheatsheet


def dc_extract_cheatsheet_unstripped_rfind(response: str, old_cheatsheet: str) -> str:
    """Unstripped rfind — corrupts when <think> has a closed <cheatsheet> example and body truncates!"""
    end_idx = response.rfind("</cheatsheet>")
    if end_idx == -1:
        return old_cheatsheet
    start_idx = response.rfind("<cheatsheet>", 0, end_idx)
    if start_idx == -1:
        return old_cheatsheet
    candidate = response[start_idx + len("<cheatsheet>") : end_idx].strip()
    return candidate if candidate else old_cheatsheet


def dc_extract_cheatsheet_atomic_cas(response: str, old_cheatsheet: str) -> str:
    """Hardened CAS extractor:
    1) Rejects responses truncated inside an unclosed <think> block;
    2) Strips any completed </think> reasoning preamble before scanning;
    3) Rejects if a trailing unclosed <cheatsheet> follows the last </cheatsheet>.
    """
    last_open_think = response.rfind("<think>")
    last_close_think = response.rfind("</think>")
    if last_open_think > last_close_think:
        return old_cheatsheet
    body = response[last_close_think + len("</think>") :] if last_close_think != -1 else response

    end_idx = body.rfind("</cheatsheet>")
    if end_idx == -1:
        return old_cheatsheet
    if body.find("<cheatsheet>", end_idx + len("</cheatsheet>")) != -1:
        return old_cheatsheet
    start_idx = body.rfind("<cheatsheet>", 0, end_idx)
    if start_idx == -1:
        return old_cheatsheet
    candidate = body[start_idx + len("<cheatsheet>") : end_idx].strip()
    return candidate if candidate else old_cheatsheet


def expel_parse_rules_pinned(llm_text: str) -> list[tuple[str, str]]:
    """Exact reproduction of LeapLabTHU/ExpeL@e41ec9a248 agent/expel.py:665-681."""
    pattern = r"((?:REMOVE|EDIT|ADD|AGREE)(?: \d+|)): (?:[a-zA-Z\s\d]+: |)(.*)"
    matches = re.findall(pattern, llm_text)
    res = []
    banned_words = ["ADD", "AGREE", "EDIT"]
    for operation, text in matches:
        text = text.strip()
        if text != "" and not any(w in text for w in banned_words) and text.endswith("."):
            if "ADD" in operation:
                res.append(("ADD", text))
            else:
                res.append((operation.strip(), text))
    return res


def expel_retrieve_rule_index_pinned(
    rules: list[tuple[str, int]], operation: tuple[str, str]
) -> int | None:
    """Exact reproduction of LeapLabTHU/ExpeL@e41ec9a248 agent/expel.py:683-687."""
    operation_rule_text = operation[1]
    for i in range(len(rules)):
        if rules[i][0] in operation_rule_text:
            return i
    return None


def expel_is_existing_rule_pinned(
    rules: list[tuple[str, int]], operation_rule_text: str
) -> bool:
    """Exact reproduction of LeapLabTHU/ExpeL@e41ec9a248 agent/expel.py:689-693."""
    for i in range(len(rules)):
        if rules[i][0] in operation_rule_text:
            return True
    return False


def expel_update_rules_pinned(
    rules: list[tuple[str, int]],
    operations: list[tuple[str, str]],
    list_full: bool = False,
) -> list[tuple[str, int]]:
    """Exact reproduction of LeapLabTHU/ExpeL@e41ec9a248 agent/expel.py:696-743."""
    rules = list(rules)
    operations = list(operations)
    delete_indices = []
    for i in range(len(operations)):
        operation, operation_rule_text = operations[i]
        operation_type = operation.split(" ")[0]
        rule_num = int(operation.split(" ")[1]) if " " in operation else None

        if operation_type == "ADD":
            if expel_is_existing_rule_pinned(rules, operation_rule_text):
                delete_indices.append(i)
        else:
            if operation_type == "EDIT":
                if expel_is_existing_rule_pinned(rules, operation_rule_text):
                    rule_num = expel_retrieve_rule_index_pinned(
                        rules, (operation, operation_rule_text)
                    )
                    assert rule_num is not None
                    operations[i] = (f"AGREE {rule_num+1}", rules[rule_num][0])
                elif (rule_num is None) or (rule_num > len(rules)):
                    delete_indices.append(i)
            elif operation_type in ("REMOVE", "AGREE"):
                if not expel_is_existing_rule_pinned(rules, operation_rule_text):
                    delete_indices.append(i)

    operations = [operations[i] for i in range(len(operations)) if i not in delete_indices]

    for op in ["REMOVE", "AGREE", "EDIT", "ADD"]:
        for i in range(len(operations)):
            operation, operation_rule_text = operations[i]
            operation_type = operation.split(" ")[0]
            if operation_type != op:
                continue
            if operation_type == "REMOVE":
                rule_index = expel_retrieve_rule_index_pinned(
                    rules, (operation, operation_rule_text)
                )
                assert rule_index is not None
                remove_strength = 3 if list_full else 1
                rules[rule_index] = (
                    rules[rule_index][0],
                    rules[rule_index][1] - remove_strength,
                )
            elif operation_type == "AGREE":
                rule_index = expel_retrieve_rule_index_pinned(
                    rules, (operation, operation_rule_text)
                )
                assert rule_index is not None
                rules[rule_index] = (rules[rule_index][0], rules[rule_index][1] + 1)
            elif operation_type == "EDIT":
                rule_index = int(operation.split(" ")[1]) - 1
                rules[rule_index] = (operation_rule_text, rules[rule_index][1] + 1)
            elif operation_type == "ADD":
                rules.append((operation_rule_text, 2))
    rules = [rules[i] for i in range(len(rules)) if rules[i][1] > 0]
    rules.sort(key=lambda x: x[1], reverse=True)
    return rules


SKILLDIFF_MARK = "**[FOCUS]**"
SKILLDIFF_NOTE = (
    "> **Items marked `[FOCUS]`.** Pay particular attention to the items marked `[FOCUS]` below. "
    "When you plan the corresponding steps, carry their specific procedures, tools, parameters, "
    "conditions, and exceptions into your plan as written, instead of simplifying them to a "
    "generic approach."
)
SKILLDIFF_BODY_TYPES = {"list entry", "paragraph", "code block", "table"}
SKILLDIFF_LIST_RE = re.compile(r"^(\s*(?:>\s*)*)([-*+]|\d+[.)])(\s+)(\[[ xX]\]\s+)?")


def skilldiff_mark_pinned(
    original: str, items: list[dict[str, object]], coverage: dict[int, int]
) -> str:
    """Exact reproduction of LitaoGuo/How-Self-Evolution-Reshapes-Skills@db2cdbde29 skilldiff.py:22-47."""
    newline = "\r\n" if "\r\n" in original else "\n"
    fm_match = re.match(r"\A---\r?\n.*?\r?\n---\r?\n", original, flags=re.DOTALL)
    front = fm_match.group(0) if fm_match else ""
    body = original[len(front) :]
    first = re.search(r"\S", body)
    position = len(front) + (first.start() if first else 0)
    title = re.match(r"#[ \t]+[^\r\n]*(?:\r?\n|$)", original[position:])
    if title:
        position += title.end()
    edits: list[tuple[int, str]] = [(position, newline + SKILLDIFF_NOTE + newline + newline)]
    for item in items:
        item_id = int(item["id"])  # type: ignore[arg-type]
        if item["type"] not in SKILLDIFF_BODY_TYPES or coverage[item_id] != 0:
            continue
        pos = int(item["start"])  # type: ignore[arg-type]
        end = int(item["end"])  # type: ignore[arg-type]
        text = str(item["text"])
        if original[pos:end] != text:
            raise ValueError(f"Original item {item_id} no longer matches.")
        marker = SKILLDIFF_LIST_RE.match(text) if item["type"] == "list entry" else None
        if marker:
            edits.append((pos + marker.end(), SKILLDIFF_MARK + " "))
        else:
            indentation = re.match(r"[ \t]*", text).group()  # type: ignore[union-attr]
            edits.append((pos, indentation + SKILLDIFF_MARK + newline + newline))
    result = original
    for pos, ins_text in reversed(sorted(edits, key=lambda edit: edit[0])):
        result = result[:pos] + ins_text + result[pos:]
    return result


@dataclass(frozen=True)
class SammoSymbolicNode:
    """Pure-stdlib symbolic AST faithfully mirroring microsoft/sammo@736552381d
    DocumentComponent (Section/Paragraph/MetaPrompt, with .content and .static_text())
    vs. InputData / FewshotExamples (instructions.py:170-188, 257-269, lacking .content
    and .static_text()).
    """

    kind: str
    title: str | None = None
    content: tuple[SammoSymbolicNode, ...] | str | None = None
    reference_id: str | None = None
    reference_classes: tuple[str, ...] = field(default_factory=tuple)

    def sym_hasattr_content(self) -> bool:
        return self.kind in ("MetaPrompt", "Section", "Paragraph")

    def static_text(self) -> str:
        if not self.sym_hasattr_content():
            raise AttributeError(f"'{self.kind}' object has no attribute 'static_text'")
        if isinstance(self.content, str):
            return self.content
        if isinstance(self.content, tuple):
            return "\n".join(child.static_text() for child in self.content)
        return ""

    def render_markdown(self) -> str:
        if isinstance(self.content, str):
            body = self.content
        elif isinstance(self.content, tuple):
            body = "\n\n".join(child.render_markdown() for child in self.content)
        else:
            body = "<dynamic-input-slot>"
        if self.title:
            return f"## {self.title}\n{body}"
        return body

    def find_paths(self, css_selector: str, prefix: str = "") -> list[tuple[str, SammoSymbolicNode]]:
        matches: list[tuple[str, SammoSymbolicNode]] = []
        if css_selector.startswith("#") and self.reference_id == css_selector[1:]:
            matches.append((prefix, self))
        elif css_selector.startswith(".") and css_selector[1:] in self.reference_classes:
            matches.append((prefix, self))
        if isinstance(self.content, tuple):
            for idx, child in enumerate(self.content):
                cpath = f"{prefix}.content[{idx}]"
                matches.extend(child.find_paths(css_selector, cpath))
        return matches


def sammo_rewrite_mutate_pinned(
    root: SammoSymbolicNode, css_selector: str, rewrite_prefix: str
) -> SammoSymbolicNode:
    """Line-accurate mirror of microsoft/sammo@736552381d sammo/mutators.py:379-386 Rewrite.mutate:
      L379: matches = candidate.find_all(self._css_selector)
      L380: segment_paths = [m.path + ".content" if m.node.sym_hasattr("content") else "" for m in matches]
      L381: segment_content = matches[0].node.static_text()
      L382: rewritten = await self._rewrite(runner, segment_content, ...)
      L384: pg.clone(candidate, override={p: r for p in segment_paths})
    """
    matches = root.find_paths(css_selector)
    segment_paths = [
        f"{path}.content" if node.sym_hasattr_content() else "" for path, node in matches
    ]
    # L381: raises AttributeError immediately if matches[0] is InputData/FewshotExamples,
    # AND ignores matches[1:] text when multiple .tunable sections match!
    segment_content = matches[0][1].static_text()
    rewritten_text = f"{rewrite_prefix}: {segment_content}"
    override_paths = {p: rewritten_text for p in segment_paths}

    if "" in override_paths:
        return SammoSymbolicNode(kind="ClobberedRoot", content=override_paths[""])

    def apply_rec(node: SammoSymbolicNode, cur_path: str) -> SammoSymbolicNode:
        if f"{cur_path}.content" in override_paths:
            return SammoSymbolicNode(
                kind=node.kind,
                title=node.title,
                content=override_paths[f"{cur_path}.content"],
                reference_id=node.reference_id,
                reference_classes=node.reference_classes,
            )
        if isinstance(node.content, tuple):
            return SammoSymbolicNode(
                kind=node.kind,
                title=node.title,
                content=tuple(
                    apply_rec(c, f"{cur_path}.content[{i}]") for i, c in enumerate(node.content)
                ),
                reference_id=node.reference_id,
                reference_classes=node.reference_classes,
            )
        return node

    return apply_rec(root, "")


def run_probe_3() -> None:
    print("\n" + "=" * 78)
    print("PROBE 3: Exact Source Bugs (Dynamic Cheatsheet, ExpeL, SkillDiff, SAMMO)")
    print("  Banner: [exact reproduction of pinned source bugs]")
    print("=" * 78)

    # 1. Dynamic Cheatsheet@5cfe3c37e8 extractor.py:78-86 across 7 categories (N=350)
    old_mem = "RULE_1: Verify modular inverse.\nRULE_2: Check boundary n=0."
    categories = (
        "clean",
        "truncated",
        "preamble_unclosed",
        "think_example_then_trunc",
        "think_example_then_absent",
        "think_unclosed_trunc",
        "absent",
    )
    corpus: list[tuple[str, str, str]] = []
    for k in range(50):
        clean_new = f"{old_mem}\nRULE_3_{k}: Use CRT."
        corpus.append(("clean", f"Update:\n<cheatsheet>\n{clean_new}\n</cheatsheet>", clean_new))
        corpus.append(("truncated", "Update:\n<cheatsheet>\nRULE_1: Verify mod inv", old_mem))
        corpus.append(
            (
                "preamble_unclosed",
                f"<think>I must output a <cheatsheet> block next.</think>\n"
                f"<cheatsheet>\n{clean_new}\n</cheatsheet>",
                clean_new,
            )
        )
        # Adversarial Case 1: closed <cheatsheet> example inside <think>, truncated final <cheatsheet>
        corpus.append(
            (
                "think_example_then_trunc",
                "<think>Schema example: <cheatsheet>EXAMPLE_ONLY</cheatsheet></think>\n"
                "Update:\n<cheatsheet>\nRULE_1: truncated at max_tokens",
                old_mem,
            )
        )
        # Adversarial Case 2: closed <cheatsheet> example inside <think>, no cheatsheet in final answer
        corpus.append(
            (
                "think_example_then_absent",
                "<think>Recall <cheatsheet>STALE_DRAFT</cheatsheet> tag syntax.</think>\n"
                "No memory changes needed.",
                old_mem,
            )
        )
        # Adversarial Case 3: response hits max_tokens mid-<think> after mentioning <cheatsheet>
        corpus.append(
            (
                "think_unclosed_trunc",
                "<think>Drafting <cheatsheet>UNFINISHED_THOUGHT</cheatsheet> wait let me check",
                old_mem,
            )
        )
        corpus.append(("absent", "No memory changes needed.", old_mem))

    corrupt_pinned = {c: 0 for c in categories}
    corrupt_regex = {c: 0 for c in categories}
    corrupt_rfind = {c: 0 for c in categories}
    corrupt_atomic = {c: 0 for c in categories}
    for kind, resp, expected in corpus:
        if dc_extract_cheatsheet_pinned(resp, old_mem) != expected:
            corrupt_pinned[kind] += 1
        if dc_extract_cheatsheet_naive_regex(resp, old_mem) != expected:
            corrupt_regex[kind] += 1
        if dc_extract_cheatsheet_unstripped_rfind(resp, old_mem) != expected:
            corrupt_rfind[kind] += 1
        if dc_extract_cheatsheet_atomic_cas(resp, old_mem) != expected:
            corrupt_atomic[kind] += 1

    assert sum(corrupt_pinned.values()) == 250
    assert sum(corrupt_regex.values()) == 200
    assert sum(corrupt_rfind.values()) == 150  # fails all 3 <think>-example adversarial categories!
    assert sum(corrupt_atomic.values()) == 0

    # 2. ExpeL@e41ec9a248 substring collision (L683-741) + fold enumeration bug (L369-374)
    seed_rules = [
        ("Check table headers.", 2),
        ("Verify units before subtracting.", 2),
    ]
    critique_text = (
        "ADD: Check table headers. Cast numeric columns to float before summing.\n"
        "EDIT 2: Normalize currencies first, then Check table headers."
    )
    ops = expel_parse_rules_pinned(critique_text)
    updated_expel = expel_update_rules_pinned(seed_rules, ops, list_full=False)
    assert updated_expel == [
        ("Check table headers.", 3),
        ("Verify units before subtracting.", 2),
    ], f"Unexpected ExpeL result: {updated_expel}"

    succeeded_trial_history = {f"task_{tid}": ["traj"] for tid in [2, 5, 8, 10, 11, 12]}
    task2idx = {f"task_{tid}": tid for tid in [2, 5, 8, 10, 11, 12]}
    training_ids_fold2 = [10, 11, 12]
    buggy_all_success = [
        task for idx, task in enumerate(succeeded_trial_history) if idx in training_ids_fold2
    ]
    fixed_all_success = [
        task for task in succeeded_trial_history if task2idx[task] in training_ids_fold2
    ]
    assert len(buggy_all_success) == 0 and len(fixed_all_success) == 3

    # 3. SkillDiff@db2cdbde29 byte-exact reversibility
    sample_skill = (
        "---\nname: xlsx-audit\ndescription: Audit workbooks safely.\n---\n"
        "# Workbook Forensics\n\n"
        "- Run `recalc.py` with `--strict-formulas` before reading cached values.\n"
        "- Format numbers cleanly.\n\n"
        "Always check hidden sheets with `ws.sheet_state != 'visible'`.\n"
    )
    idx_li1 = sample_skill.index("- Run `recalc.py`")
    idx_li2 = sample_skill.index("- Format numbers cleanly.")
    idx_p1 = sample_skill.index("Always check hidden")
    items = [
        {
            "id": 0,
            "type": "list entry",
            "start": idx_li1,
            "end": idx_li2 - 1,
            "text": sample_skill[idx_li1 : idx_li2 - 1],
        },
        {
            "id": 1,
            "type": "list entry",
            "start": idx_li2,
            "end": idx_p1 - 2,
            "text": sample_skill[idx_li2 : idx_p1 - 2],
        },
        {
            "id": 2,
            "type": "paragraph",
            "start": idx_p1,
            "end": len(sample_skill) - 1,
            "text": sample_skill[idx_p1 : len(sample_skill) - 1],
        },
    ]
    marked = skilldiff_mark_pinned(sample_skill, items, coverage={0: 0, 1: 10, 2: 0})
    unmarked = (
        marked.replace("\n" + SKILLDIFF_NOTE + "\n\n", "", 1)
        .replace(SKILLDIFF_MARK + "\n\n", "")
        .replace(SKILLDIFF_MARK + " ", "")
    )
    assert hashlib.sha256(unmarked.encode()).hexdigest() == hashlib.sha256(
        sample_skill.encode()
    ).hexdigest()

    # 4. SAMMO@736552381d Rewrite.mutate (mutators.py:379-386):
    #    (a) Unique #id selector -> 0/100 byte drift on #frozen_schema AND sibling #verification;
    #    (b) Targeting InputData (#input_slot) directly -> raises AttributeError at mutators.py:381;
    #    (c) Multi-match class selector (.tunable across 2 Sections) -> overwrites Section 2 with
    #        Section 1's rewrite (mutators.py:381-385)!
    frozen_sec = SammoSymbolicNode(
        kind="Section",
        title="Safety & Tool Schema",
        content='{"type": "object", "required": ["patch", "test_cmd"]}',
        reference_id="frozen_schema",
        reference_classes=("invariant",),
    )
    heur_sec = SammoSymbolicNode(
        kind="Section",
        title="Search Heuristics",
        content="Inspect logs and isolate minimal fault.",
        reference_id="heuristics",
        reference_classes=("tunable",),
    )
    verif_sec = SammoSymbolicNode(
        kind="Section",
        title="Verification Policy",
        content="Run deterministic unit tests before returning.",
        reference_id="verification",
        reference_classes=("tunable",),
    )
    input_slot = SammoSymbolicNode(
        kind="InputData",
        title=None,
        content=None,
        reference_id="input_slot",
        reference_classes=("mixed_bad",),
    )
    mixed_sec = SammoSymbolicNode(
        kind="Section",
        title="Preamble",
        content="Task context:",
        reference_id="preamble",
        reference_classes=("mixed_bad",),
    )
    root_ast = SammoSymbolicNode(
        kind="MetaPrompt",
        content=(frozen_sec, heur_sec, verif_sec, mixed_sec, input_slot),
        reference_id="root",
    )
    frozen_sha_before = hashlib.sha256(frozen_sec.render_markdown().encode()).hexdigest()
    verif_sha_before = hashlib.sha256(verif_sec.render_markdown().encode()).hexdigest()

    cur_ast = root_ast
    for step in range(100):
        cur_ast = sammo_rewrite_mutate_pinned(cur_ast, "#heuristics", f"v{step}")
        cur_frozen = cur_ast.find_paths("#frozen_schema")[0][1]
        cur_verif = cur_ast.find_paths("#verification")[0][1]
        assert (
            hashlib.sha256(cur_frozen.render_markdown().encode()).hexdigest() == frozen_sha_before
        )
        assert hashlib.sha256(cur_verif.render_markdown().encode()).hexdigest() == verif_sha_before

    # Direct #input_slot target raises AttributeError at mutators.py:381 (.static_text())
    raised_attr_error = False
    try:
        sammo_rewrite_mutate_pinned(root_ast, "#input_slot", "bad")
    except AttributeError:
        raised_attr_error = True
    assert raised_attr_error, "InputData lacks .static_text() and must raise AttributeError at L381"

    # Multi-match .tunable class selector silently overwrites #verification with #heuristics's rewrite!
    multi_mutated = sammo_rewrite_mutate_pinned(root_ast, ".tunable", "REWRITTEN")
    m_heur = multi_mutated.find_paths("#heuristics")[0][1]
    m_verif = multi_mutated.find_paths("#verification")[0][1]
    assert m_verif.content == m_heur.content == "REWRITTEN: Inspect logs and isolate minimal fault."

    # Multi-match where matches[0] is Section and matches[1] is InputData hits L380 "" fallback at L384
    mixed_clobber = sammo_rewrite_mutate_pinned(root_ast, ".mixed_bad", "CLOBBER")
    assert mixed_clobber.kind == "ClobberedRoot"

    print(
        f"  [3A] Dynamic Cheatsheet extractor (N=350 across 7 adversarial classes): "
        f"pinned=250/350 | naive_regex=200/350 | unstripped_rfind=150/350 | "
        f"think-stripped CAS=0/350 corruptions"
    )
    print(
        f"  [3B] ExpeL bugs: substring match dropped 1/1 extended ADD & hijacked EDIT 2 -> AGREE 1; "
        f"L371 enumerate bug yielded {len(buggy_all_success)}/3 fold-2 success traces"
    )
    print(
        f"  [3C] SkillDiff + SAMMO@736552381d: 100% SHA-256 recovery on SkillDiff strip; "
        f"0/100 drift on #frozen_schema & #verification under unique #heuristics selector; "
        f"verified L381 AttributeError on #input_slot & L381-385 multi-match .tunable overwrite"
    )


# =============================================================================
# PROBE 4: Instruction-Conflict Bayes Crossover & 3-Regime Negation Bifurcation
# =============================================================================


def sigmoid(x: float) -> float:
    return 1.0 / (1.0 + math.exp(-x))


def exact_fisher_2x2_two_sided(a: int, b: int, c: int, d: int) -> float:
    """Exact two-sided Fisher test p-value via hypergeometric probability sum."""
    r1, r2 = a + b, c + d
    c1 = a + c
    n = r1 + r2

    def hypergeom_p(k: int) -> float:
        return (math.comb(r1, k) * math.comb(r2, c1 - k)) / math.comb(n, c1)

    p_obs = hypergeom_p(a)
    k_min = max(0, c1 - r2)
    k_max = min(r1, c1)
    return sum(hypergeom_p(k) for k in range(k_min, k_max + 1) if hypergeom_p(k) <= p_obs + 1e-12)


def mann_whitney_two_sided_exact(xs: list[float], ys: list[float]) -> float:
    """Exact permutation two-sided Mann-Whitney U p-value for small samples (18 items)."""
    pooled = xs + ys
    n_x = len(xs)
    n_tot = len(pooled)
    sorted_vals = sorted(pooled)
    ranks = []
    for v in pooled:
        idxs = [i + 1 for i, sv in enumerate(sorted_vals) if sv == v]
        ranks.append(sum(idxs) / len(idxs))

    obs_sum = sum(ranks[:n_x])
    mean_sum = n_x * (n_tot + 1) / 2.0
    obs_dev = abs(obs_sum - mean_sum)
    extreme = 0
    total = 0
    for comb in itertools.combinations(range(n_tot), n_x):
        total += 1
        s = sum(ranks[i] for i in comb)
        if abs(s - mean_sum) >= obs_dev - 1e-12:
            extreme += 1
    return extreme / total


def run_probe_4() -> None:
    print("\n" + "=" * 78)
    print("PROBE 4: Conflict Bayes Crossover & 3-Regime Negation Polarity Bifurcation")
    print("  4A Banner: [exact analytical / derived calculation] (matched denominators only)")
    print("  4B Banner: [exact analytical / derived calculation] + [toy model / illustrative mechanism]")
    print("=" * 78)

    # --- Part 4A: Bayes Break-Even Prevalence pi*(lambda) ONLY where clean d_alpha is measured ---
    # ConInstruct Table 3 (arXiv:2511.14342v2):
    #   GPT-4o:      d_alpha = 0.40 (false clarify on clean I_0), d_beta = 0.97 - 0.04 = 0.93
    #   GPT-4o-mini: d_alpha = 0.53, d_beta = 0.98 - 0.04 = 0.94
    # DUET Table 1 (arXiv:2608.14644v1):
    #   Qwen3-8B forced self-cue prefix: d_alpha = 0.860 - 0.460 = 0.400, d_beta = 0.802 - 0.645 = 0.157
    #   DUET-8B distilled vs Teacher*:   d_alpha = 0.860 - 0.910 = -0.050 (<0), d_beta = 0.852 - 0.645 = 0.207
    def break_even_pi(d_alpha: float, d_beta: float, lam: float) -> float:
        if d_alpha <= 0 and d_beta > 0:
            return 0.0
        return d_alpha / (d_alpha + lam * d_beta)

    pi_gp_4o_l1 = break_even_pi(0.40, 0.93, 1.0)
    pi_gp_4o_l5 = break_even_pi(0.40, 0.93, 5.0)
    pi_gp_mini_l1 = break_even_pi(0.53, 0.94, 1.0)
    pi_duet_pref_l1 = break_even_pi(0.400, 0.157, 1.0)
    pi_duet_pref_l5 = break_even_pi(0.400, 0.157, 5.0)
    pi_duet_8b = break_even_pi(-0.050, 0.207, 1.0)

    # WhoWins (arXiv:2610.33201v1 Table 3 & App. M Table 21): strictly within-experiment,
    # matched-denominator deltas (Tiers has 0 conflict-free trials -> d_alpha & pi* unmeasured!).
    ww_27b_tiers_dec_off, ww_27b_tiers_dec_on = 0.9391, 0.9851
    ww_27b_tiers_use_off, ww_27b_tiers_use_on = 0.8210, 0.8708
    ww_35b_tiers_dec_off, ww_35b_tiers_dec_on = 0.6793, 0.9364
    ww_122b_tiers_dec_off, ww_122b_tiers_dec_on = 0.7567, 0.9544
    ww_27b_dec_delta = ww_27b_tiers_dec_on - ww_27b_tiers_dec_off
    ww_27b_use_delta = ww_27b_tiers_use_on - ww_27b_tiers_use_off
    ww_35b_dec_delta = ww_35b_tiers_dec_on - ww_35b_tiers_dec_off
    ww_122b_dec_delta = ww_122b_tiers_dec_on - ww_122b_tiers_dec_off

    assert abs(pi_gp_4o_l1 - 0.30075188) < 1e-6
    assert abs(pi_duet_pref_l1 - 0.71813285) < 1e-6
    assert pi_duet_8b == 0.0
    assert abs(ww_27b_dec_delta - 0.0460) < 1e-6 and abs(ww_27b_use_delta - 0.0498) < 1e-6
    assert abs(ww_35b_dec_delta - 0.2571) < 1e-6 and abs(ww_122b_dec_delta - 0.1977) < 1e-6

    print("  [4A] Break-even conflict prevalence pi*(lambda = L_viol / L_false_block):")
    print(
        f"       ConInstruct GP (GPT-4o, 40% I_0 false-clarify): pi*(1)={pi_gp_4o_l1*100:.2f}%, "
        f"pi*(5)={pi_gp_4o_l5*100:.2f}% | GPT-4o-mini (53%): pi*(1)={pi_gp_mini_l1*100:.2f}%"
    )
    print(
        f"       DUET Qwen3-8B forced self-cue prefix (-40.0 pp benign util): pi*(1)={pi_duet_pref_l1*100:.2f}%, "
        f"pi*(5)={pi_duet_pref_l5*100:.2f}% | DUET-8B distilled: pi*={pi_duet_8b*100:.2f}% (Pareto-dominant)"
    )
    print(
        f"       WhoWins within-Tiers (thinking off->on, matched denominators; clean I_0 unmeasured, R(0.95)<=1): "
        f"27B decided {ww_27b_tiers_dec_off*100:.2f}%->{ww_27b_tiers_dec_on*100:.2f}% (+{ww_27b_dec_delta*100:.2f} pp), "
        f"usable {ww_27b_tiers_use_off*100:.2f}%->{ww_27b_tiers_use_on*100:.2f}% (+{ww_27b_use_delta*100:.2f} pp); "
        f"35B decided +{ww_35b_dec_delta*100:.2f} pp; 122B decided +{ww_122b_dec_delta*100:.2f} pp "
        f"(vs Ladder Operator-first 34.67% decided on 27B)"
    )

    # --- Part 4B.1: Exact primary statistical checks ---
    p_viol_01 = sigmoid(-2.40 + 2.27 * 0.10)
    p_viol_05 = sigmoid(-2.40 + 2.27 * 0.50)
    p_viol_09 = sigmoid(-2.40 + 2.27 * 0.90)
    p_viol_10 = sigmoid(-2.40 + 2.27 * 1.00)
    assert 0.10 < p_viol_01 < 0.11 and 0.41 < p_viol_09 < 0.42 and 0.46 < p_viol_10 < 0.47

    neg_deltas = [20.0, 8.6, 5.7, -2.9, -2.9]  # Rules 6, 17, 15, 16, 18
    pos_deltas = [2.9, 2.9, 2.9, 0.0, 0.0, 0.0, 0.0, 0.0, -2.9, -8.6, -11.4, -14.3, -14.3]

    def polarity_fisher_at_cutoff(cutoff: float) -> tuple[int, int, int, int, float]:
        neg_shape = sum(1 for x in neg_deltas if x > cutoff)
        neg_dist = sum(1 for x in neg_deltas if x < -cutoff)
        pos_shape = sum(1 for x in pos_deltas if x > cutoff)
        pos_dist = sum(1 for x in pos_deltas if x < -cutoff)
        return (
            neg_shape,
            neg_dist,
            pos_shape,
            pos_dist,
            exact_fisher_2x2_two_sided(neg_shape, neg_dist, pos_shape, pos_dist),
        )

    _, _, _, _, p_cut3 = polarity_fisher_at_cutoff(3.0)
    ns5, nd5, ps5, pd5, p_cut5 = polarity_fisher_at_cutoff(5.0)
    _, _, _, _, p_cut7 = polarity_fisher_at_cutoff(7.0)
    _, _, _, _, p_cut10 = polarity_fisher_at_cutoff(10.0)
    p_mw18 = mann_whitney_two_sided_exact(neg_deltas, pos_deltas)

    assert (ns5, nd5, ps5, pd5) == (3, 0, 0, 4) and abs(p_cut5 - 1.0 / 35.0) < 1e-9
    assert abs(p_cut3 - 1.0 / 35.0) < 1e-9
    assert abs(p_cut7 - 1.0 / 15.0) < 1e-9
    assert abs(p_cut10 - 0.25) < 1e-9
    assert 0.11 < p_mw18 < 0.15  # Paper §6.4 reports Mann-Whitney p = 0.1299

    # --- Part 4B.2: [toy model / illustrative mechanism] ONLY (not empirical measurements) ---
    # Illustrative 5-slot i.i.d. hazard extrapolation & conceptual PBRS action-pruning diagram
    p_comp_5_toy = 1.0 - (1.0 - p_viol_05) ** 5

    def simulate_coding_mdp(rule_mode: str, requires_cross_file: bool = False) -> float:
        rng = random.Random(SEED + det_seed(rule_mode) % 997 + int(requires_cross_file) * 13)
        episodes = 2500
        wins = 0
        for _ in range(episodes):
            budget = 6
            fixed_target = False
            fixed_companion = not requires_cross_file
            broke_unrelated = False
            for _step in range(budget):
                if rule_mode == "no_rules":
                    p_target, p_comp, p_unrel, _p_detour = 0.42, 0.22, 0.18, 0.18
                elif rule_mode == "neg_scope_guardrail":
                    p_target, p_comp, p_unrel, _p_detour = 0.60, 0.05, 0.03, 0.32
                elif rule_mode == "pos_style_directive":
                    p_target, p_comp, p_unrel, _p_detour = 0.31, 0.18, 0.24, 0.27
                else:
                    raise ValueError(rule_mode)
                u = rng.random()
                if u < p_target:
                    if rng.random() < 0.55:
                        fixed_target = True
                elif u < p_target + p_comp:
                    if rng.random() < 0.60:
                        fixed_companion = True
                elif u < p_target + p_comp + p_unrel:
                    if rng.random() < 0.45:
                        broke_unrelated = True
            if fixed_target and fixed_companion and not broke_unrelated:
                wins += 1
        return wins / episodes

    mdp_base = simulate_coding_mdp("no_rules", False)
    mdp_neg = simulate_coding_mdp("neg_scope_guardrail", False)
    mdp_pos = simulate_coding_mdp("pos_style_directive", False)
    mdp_mig_base = simulate_coding_mdp("no_rules", True)
    mdp_mig_neg = simulate_coding_mdp("neg_scope_guardrail", True)

    assert mdp_neg > mdp_base > mdp_pos
    assert mdp_mig_neg < mdp_mig_base

    print(
        f"  [4B] [exact analytical] Semantic Gravity Wells (Qwen2.5-7B single-word): "
        f"P_0=0.10 -> {p_viol_01*100:.2f}% (obs bin 9.1%), P_0=0.90 -> {p_viol_09*100:.2f}%, "
        f"P_0=1.00 -> {p_viol_10*100:.2f}% (obs [0.8,1] bin 46.3%)"
    )
    print(
        f"       [exact analytical] Guardrails Beat Guidance (Opus 4.6, n=35, 18 rules): "
        f"Fisher p(|d|>3/5pp)={p_cut5:.4f}, p(|d|>7pp)={p_cut7:.4f}, p(|d|>10pp)={p_cut10:.4f}; "
        f"threshold-free 18-rule Mann-Whitney p={p_mw18:.4f}"
    )
    print(
        f"       [toy model / illustrative mechanism] i.i.d. 5-slot hazard at P_0=0.50 -> "
        f"{p_comp_5_toy*100:.2f}%; conceptual PBRS diagram: localized neg={mdp_neg*100:.2f}% > "
        f"base={mdp_base*100:.2f}% > pos={mdp_pos*100:.2f}% | cross-file migration neg={mdp_mig_neg*100:.2f}% < base={mdp_mig_base*100:.2f}%"
    )


def main() -> None:
    print(
        "CONTINUAL SKILL ACQUISITION & PORTFOLIO INTERFERENCE PROBES (SEED=20261121, ZERO NETWORK)"
    )
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    print("\nALL 4 PROBES + DECOUPLED NEGATIVE CONTROLS PASSED DETERMINISTICALLY.")


if __name__ == "__main__":
    main()
