#!/usr/bin/env python3
"""Deterministic verification probes for structured outputs, constrained decoding,
programmatic tool calling, and high-resolution GUI grounding.

Self-contained support script for the reference report package:
  reports/agent-structured-outputs-constrained-decoding-tool-schemas-and-computer-use/

Design invariants:
- Python 3.10+ standard library only (zero third-party dependencies, zero network).
- Fixed seed (SEED = 20261121), no timestamps or wall-clock output in stdout.
- Bit-identical stdout and SHA-256 across repeated runs (`python3 -I -B`).
- Explicit epistemic banners separating exact analytical derivations, published
  empirical table decompositions, and parameterized `[toy model]` surrogates:
  * Probe 1 (`[exact analytical / Monte Carlo over stylized prefix trees]`):
      Exact GCD vs. global conditional Q_{P,G} vs. SMC on a stylized 5-bit
      instantiation of Park et al.'s asymmetric dead-end grammar G_sk, an
      asymmetric oneOf union tree, and a balanced-EFG negative control verifying
      the positive-support iff condition (P(w_i | w_{<i}) > 0). Reports both
      250-replicate marginal KL and single-run particle support-miss / TVD.
  * Probe 2 (`[published table decomposition + equal-turn-budget toy model]`):
      2A: Patel et al. (arXiv:2608.06370v1) empirical N ~= 26 crossover, verbatim
          model-specific fan-out cliffs, KV-cache prefix discount sensitivity, and
          BFCL v4 echo-return stub disclosure.
      2B: Rai (arXiv:2611.19123v1) verbatim Table 6 (n=10 descriptive) token
          ratios without invalid overflow division, plus Table 9 author-tuned
          return-shape hint deltas.
      2C: Mao et al. (arXiv:2611.01446v1) verbatim Table 5 component ablation
          (isolating on-demand schema inspection vs. persistent cells) and 3/10
          model regressions, alongside Mak et al. (arXiv:2609.11999v1) Table 1-2.
      2D: `[toy model]` Equal-LLM-turn-budget (T_max = 6 and T_max = 8) stateful
          vs. stateless error-recovery surrogate showing both low-p stateful
          recovery and high-p stateless superiority.
  * Probe 3 (`[exact 2D Gaussian-Uniform convolution geometry + semantic recall]`):
      Exact closed-form uniform cell-overlap integral min(1, w/dx)*min(1, h/dy)
      and exact 1D/2D Gaussian-Uniform convolution (replacing erroneous Gaussian
      erf approximation for uniform patch grids), uniform aspect-preserving max-side
      scaling vs. square squashing, exact variance-share attribution, same-backbone
      1-stage vs. 2-stage crop ablation, and Stage-1 semantic region-search recall.
  * Probe 4 (`[exact iterative byte-level BPE + trigger-token automaton model]`):
      True iterative rank-priority byte-level BPE preserving all 256 single-byte
      base tokens (confirming zero hard vocabulary deadlock at EXPECT_COLON while
      blocking 100% of multi-terminal canonical merges and >95% of calibrated LM
      bridge mass under k=0), plus token-ID vs. surface-delimiter triggering
      (including In-Writing*'s unique `<eos>` trigger and empirical caveats).
"""

from __future__ import annotations

import math
import random
import re
from dataclasses import dataclass

SEED = 20261121


def kl_divergence(p: dict[str, float], q: dict[str, float]) -> float:
    """Compute exact D_KL(P || Q) in nats over the positive support of P."""
    total = 0.0
    for k, pk in p.items():
        if pk <= 0.0:
            continue
        qk = q.get(k, 0.0)
        if qk <= 0.0:
            return float("inf")
        total += pk * math.log(pk / qk)
    return max(0.0, total)


def tvd(p: dict[str, float], q: dict[str, float]) -> float:
    """Compute exact Total Variation Distance 0.5 * sum_x |P(x) - Q(x)|."""
    keys = set(p.keys()) | set(q.keys())
    return 0.5 * sum(abs(p.get(k, 0.0) - q.get(k, 0.0)) for k in keys)


# =============================================================================
# PROBE 1: Greedy Constrained Decoding (GCD) vs Exact Conditional vs SMC
# =============================================================================


@dataclass(frozen=True)
class PrefixTreeLM:
    """Explicit finite-horizon autoregressive LM over a formal grammar L(G).

    `transitions[prefix]` maps next_token -> P_LM(next_token | prefix).
    `accepting` is the set of valid complete strings in L(G).
    """

    name: str
    transitions: dict[str, dict[str, float]]
    accepting: frozenset[str]

    def valid_prefixes(self) -> set[str]:
        valid: set[str] = set()
        for s in self.accepting:
            parts = s.split("|")
            for i in range(len(parts) + 1):
                valid.add("|".join(parts[:i]))
        return valid

    def exact_unconstrained_and_conditional(
        self,
    ) -> tuple[dict[str, float], dict[str, float], float]:
        """Return (P_unconstrained on L(G), P_true(. | L(G)), total_valid_mass Z)."""
        p_raw: dict[str, float] = {}
        for s in sorted(self.accepting):
            parts = s.split("|")
            prob = 1.0
            for i, tok in enumerate(parts):
                pref = "|".join(parts[:i])
                prob *= self.transitions[pref][tok]
            p_raw[s] = prob
        z = sum(p_raw.values())
        p_true = {s: v / z for s, v in p_raw.items()}
        return p_raw, p_true, z

    def exact_gcd(self) -> dict[str, float]:
        """Exact left-to-right locally renormalized Greedy Constrained Decoding."""
        vp = self.valid_prefixes()
        p_gcd: dict[str, float] = {}
        for s in sorted(self.accepting):
            parts = s.split("|")
            prob = 1.0
            for i, tok in enumerate(parts):
                pref = "|".join(parts[:i])
                trans = self.transitions[pref]
                allowed = {
                    t: pt
                    for t, pt in trans.items()
                    if (f"{pref}|{t}" if pref else t) in vp
                }
                z_local = sum(allowed.values())
                prob *= allowed[tok] / z_local if z_local > 0.0 else 0.0
            p_gcd[s] = prob
        return p_gcd

    def run_smc_once(self, num_particles: int, rng: random.Random) -> dict[str, float]:
        """Single M-particle Sequential Monte Carlo (Loula et al. 2025) rollout.

        Proposal at step t is the exact local GCD distribution q_t(a | prefix);
        the incremental importance weight is the exact local survival mass
        Z_t = sum_{a in valid(prefix)} P_LM(a | prefix), so that the product of
        incremental weights equals P_LM(x) / P_GCD(x) exactly.
        Systematic resampling triggers whenever ESS < M / 2.
        """
        vp = self.valid_prefixes()
        horizon = len(next(iter(self.accepting)).split("|"))
        particles = ["" for _ in range(num_particles)]
        log_weights = [0.0 for _ in range(num_particles)]

        for step in range(horizon):
            for idx in range(num_particles):
                pref = particles[idx]
                trans = self.transitions[pref]
                allowed_items = [
                    (t, pt)
                    for t, pt in sorted(trans.items())
                    if (f"{pref}|{t}" if pref else t) in vp and pt > 0.0
                ]
                z_local = sum(pt for _, pt in allowed_items)
                u = rng.random() * z_local
                acc = 0.0
                chosen = allowed_items[-1][0]
                for t, pt in allowed_items:
                    acc += pt
                    if u <= acc:
                        chosen = t
                        break
                particles[idx] = f"{pref}|{chosen}" if pref else chosen
                log_weights[idx] += math.log(z_local)

            max_lw = max(log_weights)
            w = [math.exp(lw - max_lw) for lw in log_weights]
            sw = sum(w)
            wn = [wi / sw for wi in w]
            ess = 1.0 / sum(wi * wi for wi in wn)

            if step < horizon - 1 and ess < 0.5 * num_particles:
                u0 = rng.random() / num_particles
                cdf = []
                c = 0.0
                for wi in wn:
                    c += wi
                    cdf.append(c)
                new_particles = []
                j = 0
                for m in range(num_particles):
                    target = u0 + m / num_particles
                    while j < num_particles - 1 and cdf[j] < target:
                        j += 1
                    new_particles.append(particles[j])
                particles = new_particles
                log_weights = [0.0 for _ in range(num_particles)]

        max_lw = max(log_weights)
        w = [math.exp(lw - max_lw) for lw in log_weights]
        sw = sum(w)
        dist: dict[str, float] = {s: 0.0 for s in self.accepting}
        for p_str, wi in zip(particles, w):
            dist[p_str] += wi / sw
        return dist


def build_stylized_5bit_lm() -> PrefixTreeLM:
    """Stylized finite-horizon prefix-tree instantiation inspired by Park et al.
    (NeurIPS 2024, arXiv:2405.21047v4) grammar G_sk:
      S ::= 00000 | 1 A_2;  A_i ::= 0 A_{i+1} | 1 A_{i+1} (i=2..4);  A_5 ::= 0 | 1.

    Note: Park et al. Fig. 2 uses P(0) = 0.45 per step and P($) = 10^-8 so
    joint P(00000$) = 0.45^5 * 10^-8, c(0) = 0.45^4 * 10^-8, c(0000) = 0.45 * 10^-8.
    Here we use less extreme stylized weights (root 0.55/0.45, EFG('0') = 0.1^4 = 1e-4,
    EFG('1') = 1.0) so M-particle SMC convergence is observable at M <= 256.
    """
    transitions: dict[str, dict[str, float]] = {"": {"0": 0.55, "1": 0.45}}
    accepting: set[str] = {"0|0|0|0|0"}

    for depth in range(1, 5):
        pref = "|".join(["0"] * depth)
        transitions[pref] = {"0": 0.10, "1": 0.90}

    def populate_one_branch(pref: str, depth: int) -> None:
        if depth == 5:
            accepting.add(pref)
            return
        p0 = 0.60 if depth % 2 == 1 else 0.35
        transitions[pref] = {"0": p0, "1": 1.0 - p0}
        populate_one_branch(f"{pref}|0", depth + 1)
        populate_one_branch(f"{pref}|1", depth + 1)

    populate_one_branch("1", 1)
    return PrefixTreeLM(
        name="Model 1A [stylized prefix tree]: 5-Bit Asymmetric Dead-End Grammar (inspired by Park G_sk)",
        transitions=transitions,
        accepting=frozenset(accepting),
    )


def build_oneof_schema_lm() -> PrefixTreeLM:
    """Stylized `oneOf` union JSON schema tree with asymmetric EFG:
    - Branch 'strict': initial prior P=0.70, downstream EFG = 0.05 * 0.40 = 0.020.
    - Branch 'flex': initial prior P=0.30, downstream EFG = 0.90 * 0.95 = 0.855.
    """
    transitions: dict[str, dict[str, float]] = {
        "": {"strict": 0.70, "flex": 0.30},
        "strict": {"digit_ok": 0.05, "bad_fmt": 0.95},
        "strict|digit_ok": {"0": 0.25, "5": 0.15, "other_invalid": 0.60},
        "flex": {"list_a": 0.50, "list_b": 0.40, "bad_type": 0.10},
        "flex|list_a": {"end_1": 0.55, "end_2": 0.40, "bad_end": 0.05},
        "flex|list_b": {"end_1": 0.65, "end_2": 0.30, "bad_end": 0.05},
    }
    accepting = frozenset(
        {
            "strict|digit_ok|0",
            "strict|digit_ok|5",
            "flex|list_a|end_1",
            "flex|list_a|end_2",
            "flex|list_b|end_1",
            "flex|list_b|end_2",
        }
    )
    return PrefixTreeLM(
        name="Model 1B [stylized prefix tree]: Asymmetric oneOf/Union Schema Grammar (Strict vs Flex)",
        transitions=transitions,
        accepting=accepting,
    )


def build_symmetric_negative_control_lm() -> PrefixTreeLM:
    """Negative Control: Prefix-symmetric grammar with 68% total dead-end mass
    pruned, EQUAL EFG (0.40) across all positive-probability valid siblings
    (P(w_i | w_{<i}) > 0), PLUS a zero-LM-probability grammatically alive branch
    ('zero_alive', P = 0.0) whose downstream EFG = 1.0 != 0.40.

    Mechanically verifies both halves of the exact zero-KL iff theorem:
      D_KL(Q_{P,G} || P_GCD) = 0  iff  all grammatically alive sibling tokens
      WITH POSITIVE LM PROBABILITY P(w_i | w_{1:i-1}) > 0 share identical EFG.
    """
    transitions: dict[str, dict[str, float]] = {
        "": {"branch_A": 0.56, "branch_B": 0.24, "zero_alive": 0.0, "invalid_root": 0.20},
        "branch_A": {"a1": 0.35, "a2": 0.15, "dead_A": 0.50},
        "branch_B": {"b1": 0.10, "b2": 0.40, "dead_B": 0.50},
        "zero_alive": {"z1": 1.00},
        "branch_A|a1": {"ok1": 0.60, "ok2": 0.20, "dead": 0.20},
        "branch_A|a2": {"ok1": 0.30, "ok2": 0.50, "dead": 0.20},
        "branch_B|b1": {"ok1": 0.40, "ok2": 0.40, "dead": 0.20},
        "branch_B|b2": {"ok1": 0.70, "ok2": 0.10, "dead": 0.20},
        "zero_alive|z1": {"ok1": 1.00},  # EFG = 1.0 != 0.40, yet P_LM(zero_alive) = 0
    }
    accepting = frozenset(
        {
            "branch_A|a1|ok1",
            "branch_A|a1|ok2",
            "branch_A|a2|ok1",
            "branch_A|a2|ok2",
            "branch_B|b1|ok1",
            "branch_B|b1|ok2",
            "branch_B|b2|ok1",
            "branch_B|b2|ok2",
            "zero_alive|z1|ok1",
        }
    )
    return PrefixTreeLM(
        name="Model 1C [NEGATIVE CONTROL]: Equal EFG=0.40 on P>0 Siblings (+ P=0 Unequal-EFG Branch)",
        transitions=transitions,
        accepting=accepting,
    )


def run_probe_1() -> None:
    print("=" * 92)
    print("PROBE 1 [exact analytical / Monte Carlo over stylized prefix trees]")
    print("Greedy Constrained Decoding (GCD) vs. Exact Conditional vs. SMC KL & Support Collapse")
    print("=" * 92)
    print(
        "  Note on Park et al. (2024) Fig. 2 literal values: P(0)=0.45/step, P($)=1e-8 -> "
        f"c(0) = 0.45^4 * 1e-8 = {(0.45**4)*1e-8:.4e}, c(0000) = 4.5e-9."
    )
    rng = random.Random(SEED)

    for model, trap_prefix in (
        (build_stylized_5bit_lm(), "0"),
        (build_oneof_schema_lm(), "strict"),
    ):
        _, p_true, z_total = model.exact_unconstrained_and_conditional()
        p_gcd = model.exact_gcd()
        kl_fwd = kl_divergence(p_true, p_gcd)
        kl_rev = kl_divergence(p_gcd, p_true)
        tvd_gcd = tvd(p_true, p_gcd)
        pos_leaves = [s for s, v in p_true.items() if v > 0.0]

        true_mass_trap = sum(
            v for k, v in p_true.items() if k.startswith(f"{trap_prefix}|")
        )
        gcd_mass_trap = sum(
            v for k, v in p_gcd.items() if k.startswith(f"{trap_prefix}|")
        )

        print(f"\n{model.name}")
        print(
            f"  Global valid mass Z = {z_total:.6f} | Positive-support leaves |L+(G)| = {len(pos_leaves)}"
        )
        print(
            f"  Trap prefix '{trap_prefix}' mass: P_true = {true_mass_trap:.6f} vs. "
            f"P_GCD = {gcd_mass_trap:.6f} ({gcd_mass_trap / true_mass_trap:.1f}x oversampling)"
        )
        print(
            f"  EXACT GCD distortion: D_KL(P_true || P_GCD) = {kl_fwd:.6f} nats | "
            f"D_KL(P_GCD || P_true) = {kl_rev:.6f} nats | TVD = {tvd_gcd:.6f}"
        )

        replicates = 250
        print(
            f"  SMC ({replicates} runs): Marginal 1-Draw KL vs. Single-Run Particle Support Collapse:"
        )
        print(
            f"  {'M':>5} | {'250-Rep Marg KL':>15} | {'Mean 1-Run TVD':>14} | "
            f"{'1-Run Leaf Miss%':>16} | {'1-Run Trap Miss%':>16} | {'Marg P(trap)':>12}"
        )
        print("  " + "-" * 90)
        smc_stats: dict[int, tuple[float, float, float]] = {}
        for m in (4, 16, 64, 256):
            agg = {s: 0.0 for s in model.accepting}
            tvds = []
            any_leaf_miss = 0
            trap_miss = 0
            for _ in range(replicates):
                emp = model.run_smc_once(m, rng)
                tvds.append(tvd(p_true, emp))
                if any(emp[s] <= 0.0 for s in pos_leaves):
                    any_leaf_miss += 1
                trap_emp = sum(
                    v for k, v in emp.items() if k.startswith(f"{trap_prefix}|")
                )
                if trap_emp <= 0.0:
                    trap_miss += 1
                for s, val in emp.items():
                    agg[s] += val / replicates
            kl_smc = kl_divergence(p_true, agg)
            mean_tvd = sum(tvds) / len(tvds)
            leaf_miss_pct = 100.0 * any_leaf_miss / replicates
            trap_miss_pct = 100.0 * trap_miss / replicates
            smc_mass_trap = sum(
                v for k, v in agg.items() if k.startswith(f"{trap_prefix}|")
            )
            smc_stats[m] = (kl_smc, mean_tvd, leaf_miss_pct)
            print(
                f"  {m:5d} | {kl_smc:15.6f} | {mean_tvd:14.6f} | "
                f"{leaf_miss_pct:15.1f}% | {trap_miss_pct:15.1f}% | {smc_mass_trap:12.6f}"
            )

        if trap_prefix == "0":
            # Verify single-run particle support collapse: on Model 1A (|L+(G)|=17),
            # M=4 single-run TVD is WORSE than deterministic GCD, and M=16 has 100% leaf-support miss!
            assert smc_stats[4][1] > tvd_gcd
            assert smc_stats[16][2] == 100.0
            assert smc_stats[256][0] < 1e-3

    ctrl = build_symmetric_negative_control_lm()
    _, p_true_c, z_c = ctrl.exact_unconstrained_and_conditional()
    p_gcd_c = ctrl.exact_gcd()
    kl_c_fwd = kl_divergence(p_true_c, p_gcd_c)
    kl_c_rev = kl_divergence(p_gcd_c, p_true_c)
    tvd_c = tvd(p_true_c, p_gcd_c)
    print(f"\n{ctrl.name}")
    print(
        f"  Global valid mass Z = {z_c:.6f} (68% dead-end pruning; P>0 siblings share EFG=0.40, "
        f"P=0 alive branch has EFG=1.0)"
    )
    print(
        f"  EXACT GCD distortion: D_KL(P_true || P_GCD) = {kl_c_fwd:.6f} nats | "
        f"D_KL(P_GCD || P_true) = {kl_c_rev:.6f} nats | TVD = {tvd_c:.6f}"
    )
    assert kl_c_fwd < 1e-12 and kl_c_rev < 1e-12 and tvd_c < 1e-12


# =============================================================================
# PROBE 2: JSON Tool Loops vs Stateless PTC vs Stateful I-PTC & Bash
# =============================================================================


def negative_binomial_completion_prob(stages: int, max_retries: int, p_stage: float) -> float:
    """Exact probability of completing `stages` sequential stateful cells with at
    most `max_retries` cell failures (total LLM turns <= stages + max_retries).
    """
    total = 0.0
    for f in range(max_retries + 1):
        total += (
            math.comb(stages + f - 1, f)
            * (p_stage**stages)
            * ((1.0 - p_stage) ** f)
        )
    return total


def run_probe_2() -> None:
    print("\n" + "=" * 92)
    print("PROBE 2 [published table decomposition + equal-turn-budget toy model]")
    print("JSON Tool Loops vs. Stateless PTC vs. Stateful I-PTC: Scale, Inspection & Turn Budget")
    print("=" * 92)

    # Part 2A: Patel et al. (arXiv:2608.06370v1) Fan-Out Anchor Audit
    # Published anchors: Sec 4.3 L338 explicitly reports empirical crossover at N ~= 26
    # across N in {7, 9, 11, 13, 15, 20, 30, 48}, with late points N=30 (3,559 JSON vs 3,380 PTC)
    # and N=48 (5,097 JSON vs 3,535 PTC).
    slope_json = (5097.0 - 3559.0) / (48.0 - 30.0)
    base_json = 3559.0 - slope_json * 30.0
    slope_ptc = (3535.0 - 3380.0) / (48.0 - 30.0)
    base_ptc = 3380.0 - slope_ptc * 30.0
    n_two_pt = (base_ptc - base_json) / (slope_json - slope_ptc)

    print("\n[Part 2A] Parallel/Sequential Fan-Out & Verbatim Model Cliffs (Patel et al., 2608.06370v1)")
    print(
        f"  Published empirical token crossover (Sec 4.3 L338, N in {{7..48}}): N ~= 26 "
        f"(2-point chord from N=30,48 gives {n_two_pt:.1f}, showing slight pre-30 curvature)."
    )
    print(
        "  Methodological disclosure (Sec 7 L490-496, L514-521): BFCL v4 uses ECHO-RETURN STUBS "
        "(no real return-schema parsing) and provider `tools`-param vs. prose billing asymmetries."
    )
    print(
        "  Verbatim published parallel-JSON recall cliffs (zero curve extrapolation):\n"
        "    * GPT-5          : holds through N=13, degrades for N > 13 (71.9% mean JSON vs 96.9% PTC on N=7..48)\n"
        "    * GPT-5.4 / 5.6  : 96.9%-100% parallel JSON sustained through N=48\n"
        "    * Claude Sonnet 5: 100% through N=70, cliff at N=70-72 (75% @ N=72, 0% @ N=100; PTC 100% @ N=100)"
    )
    print(
        f"  {'Fan-Out N':>9} | {'Seq Uncached':>12} | {'Seq 85% KV-Disc':>15} | "
        f"{'Par JSON (chord)':>16} | {'PTC (chord)':>11}"
    )
    print("  " + "-" * 76)
    for n in (1, 13, 26, 30, 48, 100):
        # Uncached sequential replays full growing prefix across N+1 turns;
        # 85% KV-cache discount charges 0.15x on replayed prefix tokens (Mak et al. 80-94% cache reads).
        seq_uncached = (n + 1) * base_json + (n * (n + 1) / 2.0) * slope_json
        replayed_tok = n * base_json + (n * (n - 1) / 2.0) * slope_json
        fresh_tok = base_json + n * slope_json
        seq_kv85 = fresh_tok + 0.15 * replayed_tok
        par_tok = base_json + n * slope_json
        ptc_tok = base_ptc + n * slope_ptc
        print(
            f"  {n:9d} | {seq_uncached:12,.0f} | {seq_kv85:15,.0f} | "
            f"{par_tok:16,.0f} | {ptc_tok:11,.0f}"
        )

    # Part 2B: Verbatim Rai (2611.19123v1) Table 6 & Table 9 Audit
    print(
        "\n[Part 2B] Verbatim Catalog Scaling & Return-Shape Hint Audit (Rai, 2611.19123v1)"
    )
    print(
        "  Table 6 scope (L390): Qwen3.8-27B, test seed 0, n = 10 tasks, serial — DESCRIPTIVE ONLY."
    )
    rai_t6 = [
        (42, 16076, 0.90, 3.4, 4112, 1.00, 3.3),
        (200, 148047, 0.80, 20.5, 7766, 1.00, 4.2),
        (2000, None, 0.00, None, 11942, 0.90, 6.0),
    ]
    print(
        f"  {'Catalog M':>9} | {'Plain MCP Tok':>14} | {'MCP Acc':>7} | "
        f"{'Code Mode Tok':>13} | {'CM Acc':>6} | {'Valid Token Savings':>22}"
    )
    print("  " + "-" * 84)
    for m, mcp_tok, mcp_acc, _t_m, cm_tok, cm_acc, _t_c in rai_t6:
        if mcp_tok is None:
            mcp_str = "OVERFLOW"
            sav_str = "N/A (MCP 0% overflow)"
        else:
            mcp_str = f"{mcp_tok:,d}"
            sav = 100.0 * (1.0 - cm_tok / mcp_tok)
            sav_str = f"{sav:5.1f}% ({mcp_tok/cm_tok:.2f}x)"
        print(
            f"  {m:9d} | {mcp_str:>14} | {100*mcp_acc:6.0f}% | "
            f"{cm_tok:13,d} | {100*cm_acc:5.0f}% | {sav_str:>22}"
        )
    print(
        "  Table 9 & Sec 5.2 (L460-464): Removing author-written, dev-tuned return-shape hints drops\n"
        "  sealed-split Code Mode by -22.7 pp (Gemma-4-26B) and -39.5 pp (Nemotron-3-30B, Holm p=0.0003),\n"
        "  flipping dev accuracy below Plain MCP (66.4% vs 83.1%; 18.5% vs 41.2%); real `outputSchema` untested."
    )

    # Part 2C: Verbatim Mao et al. (2611.01446v1) Table 5 Component Ablation & Mak et al. Cost Check
    print(
        "\n[Part 2C] Verbatim I-PTC Component Ablation (Mao et al., 2611.01446v1 Table 5) & Mak Cost Check"
    )
    mao_t5_gpt54mini = [
        ("Stateless PTC (baseline)", 59.1, 72.0, 24.0),
        ("Raw I-PTC (persistent cells ONLY)", 61.3, 129.0, 25.7),
        ("Stateless PTC + on-demand inspection", 65.8, 40.0, 8.8),
        ("Full I-PTC (persistence + inspection + docs)", 68.0, 45.0, 7.9),
    ]
    base_pass, base_raw, _ = mao_t5_gpt54mini[0][1:]
    full_pass = mao_t5_gpt54mini[-1][1]
    print(
        f"  {'GPT-5.4 mini Configuration (Mao Table 5)':<44} | {'Pass %':>7} | {'dPass':>7} | "
        f"{'Raw Tok':>8} | {'dRaw %':>8} | {'Traj Tok':>8}"
    )
    print("  " + "-" * 95)
    for name, p_acc, raw_k, traj_k in mao_t5_gpt54mini:
        dp = p_acc - base_pass
        dr = 100.0 * (raw_k - base_raw) / base_raw
        print(
            f"  {name:<44} | {p_acc:6.1f}% | {dp:+6.1f} | "
            f"{raw_k:6.0f}K | {dr:+7.1f}% | {traj_k:6.1f}K"
        )
    inspect_share = (65.8 - 59.1) / (full_pass - base_pass)
    assert inspect_share > 0.75 and mao_t5_gpt54mini[1][2] > mao_t5_gpt54mini[0][2]
    print(
        f"  -> On-demand schema inspection ALONE supplies {100*inspect_share:.1f}% (+6.7/+8.9 pp) of Full I-PTC's\n"
        "     pass lift AND lower raw tokens (40K vs 45K), whereas persistent cells alone INCREASED raw tokens\n"
        "     (+79.2% on GPT-5.4 mini: 72K->129K; +6.6% on Gemini 3.1 Flash-Lite: 122K->130K, +0.6 pp)."
    )
    print(
        "  -> Cross-model negative results (Mao Table 2): 3/10 models LOST accuracy under Full I-PTC vs Stateless PTC:\n"
        "     Claude Opus 4.7 (84.2%->82.9%), Claude Sonnet 4.6 (83.9%->80.6%), Qwen 3.5-397B (75.3%->71.8%).\n"
        "  -> Mak et al. (2609.11999v1 Table 1): Plain Bash beat PTC on score in all 4 arms (Opus-4.8 APEX: Bash 48.5%\n"
        "     > Bash+Synth 46.9% > PTC 40.1%), EXCEPT on GPT-5.5 TheAgentCompany cost ($0.56/377k Bash > $0.54/242k PTC)."
    )

    # Part 2D: [toy model] Equal-LLM-Turn-Budget Surrogate (Stateless vs Stateful + Inspection)
    print(
        "\n[Part 2D] [toy model] Equal-LLM-Turn-Budget Surrogate (K=4 Dependent Stages, Exact Turn Parity)"
    )
    print(
        "  Both regimes receive the EXACT SAME max LLM inference turn budget T_max:\n"
        "  - Stateless PTC: up to T_max full-script attempts (1 LLM turn/attempt) -> P = 1 - (1 - p^K)^T_max.\n"
        "  - Stateful I-PTC: 1 stage/cell (4 cells + at most B = T_max - K cell retries, optional cell drift c_cell).\n"
        "    Reveals BOTH regimes honestly: Stateful wins at low p (uninspected schemas, T_max=8), while Stateless\n"
        "    matches/beats Stateful at high p (strong coders / post-inspection, T_max=6) with <half the LLM turns!"
    )
    print(
        f"  {'[toy model] Regime':<38} | {'T_max':>5} | {'p_step':>6} | {'c_cell':>6} | "
        f"{'SL Pass (Turns/API)':>20} | {'SF Pass (Turns/API)':>20} | {'Delta':>7}"
    )
    print("  " + "-" * 116)

    toy_cases = [
        ("Negative Control (K=1, equal T_max=3)", 1, 3, 0.85, 0.00),
        ("Uninspected schema (low p, T_max=8)", 4, 8, 0.50, 0.00),
        ("+ On-demand inspection (p: 0.50->0.82)", 4, 8, 0.82, 0.00),
        ("Strong coder (T_max=6, zero drift)", 4, 6, 0.85, 0.00),
        ("Strong coder (T_max=6, 3% cell drift)", 4, 6, 0.85, 0.03),
    ]
    results_2d: list[float] = []
    for label, k, t_max, p_step, c_cell in toy_cases:
        # Stateless: up to t_max full monolithic attempts
        p_mono = p_step**k
        p_sl = 1.0 - (1.0 - p_mono) ** t_max
        e_turns_sl = sum((1.0 - p_mono) ** r for r in range(t_max))
        e_calls_per_try = (1.0 - p_step**k) / (1.0 - p_step) if p_step < 1.0 else float(k)
        e_api_sl = e_turns_sl * e_calls_per_try

        # Stateful: K cells + at most B = t_max - K retries (total turns <= t_max!)
        b_retries = t_max - k
        p_cell = max(0.0, p_step - c_cell)
        p_sf = negative_binomial_completion_prob(k, b_retries, p_cell)
        dp_state: dict[tuple[int, int], float] = {(0, 0): 1.0}
        e_turns_sf = 0.0
        for _ in range(t_max):
            nxt: dict[tuple[int, int], float] = {}
            for (done, fails), prob in dp_state.items():
                if done == k or fails > b_retries:
                    continue
                e_turns_sf += prob
                nxt[(done + 1, fails)] = nxt.get((done + 1, fails), 0.0) + prob * p_cell
                nxt[(done, fails + 1)] = nxt.get((done, fails + 1), 0.0) + prob * (
                    1.0 - p_cell
                )
            dp_state = nxt
        e_api_sf = e_turns_sf  # 1 stage API call per cell turn
        delta_pp = 100.0 * (p_sf - p_sl)
        results_2d.append(delta_pp)
        print(
            f"  {label:<38} | {t_max:5d} | {p_step:6.2f} | {c_cell:6.2f} | "
            f"{100*p_sl:6.1f}% ({e_turns_sl:4.2f}T/{e_api_sl:4.1f}C) | "
            f"{100*p_sf:6.1f}% ({e_turns_sf:4.2f}T/{e_api_sf:4.1f}C) | {delta_pp:+6.1f}"
        )

    # Assertions: K=1 exact parity; low-p stateful win; high-p T_max=6 stateless win!
    assert abs(results_2d[0]) < 1e-12
    assert results_2d[1] > 20.0
    assert results_2d[3] < -2.0 and results_2d[4] < -5.0


# =============================================================================
# PROBE 3: High-Resolution GUI Geometry, Uniform Cell Overlap & Semantic Recall
# =============================================================================


def exact_uniform_hit_2d(box_w: float, box_h: float, dx: float, dy: float) -> float:
    """Exact closed-form 2D hit probability under U[-dx/2, dx/2] x U[-dy/2, dy/2]
    grid quantization / patch-center snapping (ZERO Gaussian erf approximation!).
    """
    px = 1.0 if dx <= 0.0 else min(1.0, box_w / dx)
    py = 1.0 if dy <= 0.0 else min(1.0, box_h / dy)
    return px * py


def _erf_antideriv(z: float) -> float:
    """Exact antiderivative int erf(z) dz = z * erf(z) + exp(-z^2) / sqrt(pi)."""
    return z * math.erf(z) + math.exp(-(z * z)) / math.sqrt(math.pi)


def exact_gauss_unif_hit_1d(box_len: float, sigma_gauss: float, delta_unif: float) -> float:
    """Exact closed-form P(|X + U| <= box_len/2) for independent X ~ N(0, sigma^2)
    and U ~ Uniform[-delta/2, +delta/2]. Reduces continuously to exact uniform
    min(1, box_len/delta) at sigma=0 and exact erf(box_len/(2*sqrt(2)*sigma)) at delta=0.
    """
    b = 0.5 * box_len
    a = 0.5 * delta_unif
    if sigma_gauss <= 1e-12:
        return 1.0 if delta_unif <= 0.0 else min(1.0, box_len / delta_unif)
    if delta_unif <= 1e-12:
        return math.erf(b / (math.sqrt(2.0) * sigma_gauss))
    s = math.sqrt(2.0) * sigma_gauss
    z_hi = (b + a) / s
    z_lo = (b - a) / s
    # Guard large |z| against exp underflow: for |z| > 8, z*erf(z) == |z| to 64-bit machine eps
    val_hi = abs(z_hi) if abs(z_hi) > 8.0 else _erf_antideriv(z_hi)
    val_lo = abs(z_lo) if abs(z_lo) > 8.0 else _erf_antideriv(z_lo)
    return max(0.0, min(1.0, (s / delta_unif) * (val_hi - val_lo)))


def exact_gauss_unif_hit_2d(
    box_w: float,
    box_h: float,
    sigma_x: float,
    sigma_y: float,
    dx: float,
    dy: float,
) -> float:
    """Exact 2D hit probability under Gaussian head error + Uniform patch stride."""
    return exact_gauss_unif_hit_1d(box_w, sigma_x, dx) * exact_gauss_unif_hit_1d(
        box_h, sigma_y, dy
    )


def encoder_axis_scales(
    w_scr: float, h_scr: float, encoder_max_side: float, aspect_preserving: bool = True
) -> tuple[float, float]:
    """Compute native-pixels-per-encoder-pixel scale factors (scale_x, scale_y).
    - `aspect_preserving=True`: scales BOTH X and Y uniformly by max(W, H)/encoder_max_side
      (e.g., 3840x2160 -> 1024x576, scale_x = scale_y = 3.75).
    - `aspect_preserving=False`: squashes independently into encoder_max_side x encoder_max_side.
    """
    if aspect_preserving:
        s = max(1.0, max(w_scr, h_scr) / encoder_max_side)
        return s, s
    return max(1.0, w_scr / encoder_max_side), max(1.0, h_scr / encoder_max_side)


def run_probe_3() -> None:
    print("\n" + "=" * 92)
    print("PROBE 3 [exact 2D Gaussian-Uniform convolution geometry + semantic recall]")
    print("High-Res GUI Cell Overlap, Aspect-Preserving ViT Scaling & Same-Backbone 2-Stage Crop")
    print("=" * 92)

    # Part 3A: Exact Uniform Cell-Overlap Integral vs Misapplied Gaussian erf on 4K 24x24px Icon
    w4k, h4k = 3840.0, 2160.0
    dx_q, dy_q = w4k / 1000.0, h4k / 1000.0
    unif_q_24 = exact_uniform_hit_2d(24.0, 24.0, dx_q, dy_q)

    sx_ap, sy_ap = encoder_axis_scales(w4k, h4k, 1024.0, aspect_preserving=True)
    dx_ap, dy_ap = 28.0 * sx_ap, 28.0 * sy_ap  # 105.0 x 105.0 px
    unif_patch_ap = exact_uniform_hit_2d(24.0, 24.0, dx_ap, dy_ap)

    sx_sq, sy_sq = encoder_axis_scales(w4k, h4k, 1024.0, aspect_preserving=False)
    dx_sq, dy_sq = 28.0 * sx_sq, 28.0 * sy_sq  # 105.0 x 59.0625 px
    unif_patch_sq = exact_uniform_hit_2d(24.0, 24.0, dx_sq, dy_sq)

    # Compare against variance-matched Gaussian erf(w / (2*sqrt(2)*(dx/sqrt(12))))
    gauss_sq_bug = math.erf(24.0 / (2.0 * math.sqrt(2.0) * (dx_sq / math.sqrt(12.0)))) * math.erf(
        24.0 / (2.0 * math.sqrt(2.0) * (dy_sq / math.sqrt(12.0)))
    )

    # Cross-check exact_gauss_unif_hit_1d against 2000-point midpoint quadrature at intermediate sigma
    quad_n = 2000
    quad_acc = 0.0
    for i in range(quad_n):
        u = -52.5 + (i + 0.5) * (105.0 / quad_n)
        quad_acc += 0.5 * (
            math.erf((12.0 - u) / (math.sqrt(2.0) * 20.0))
            + math.erf((12.0 + u) / (math.sqrt(2.0) * 20.0))
        )
    quad_val = quad_acc / quad_n
    closed_val = exact_gauss_unif_hit_1d(24.0, 20.0, 105.0)
    assert abs(quad_val - closed_val) < 1e-7

    print("\n[Part 3A] Exact Uniform Cell-Overlap Integral on 4K (3840x2160) 24x24px Icon (sigma_head = 0)")
    print(
        f"  1. 1000-bin coord quantization ({dx_q:.2f}x{dy_q:.2f} px cell): "
        f"exact uniform hit = {100*unif_q_24:.2f}% (deterministic |err| <= 1.92px < 12px)"
    )
    print(
        f"  2. 28px merged patch @ 1024px ASPECT-PRESERVING (1024x576, stride {dx_ap:.1f}x{dy_ap:.1f} px): "
        f"exact uniform = {100*unif_patch_ap:.2f}% ((24/105)^2)"
    )
    print(
        f"  3. 28px merged patch @ 1024px SQUARE-SQUASHED (1024x1024, stride {dx_sq:.1f}x{dy_sq:.2f} px): "
        f"exact uniform = {100*unif_patch_sq:.2f}%"
    )
    print(
        f"     [Gaussian-vs-Uniform Contrast] Variance-matched Gaussian erf would falsely report {100*gauss_sq_bug:.2f}% "
        f"({gauss_sq_bug/unif_patch_sq:.2f}x over squashed, {gauss_sq_bug/unif_patch_ap:.2f}x over aspect-preserving)!"
    )
    assert abs(100 * unif_patch_ap - 5.2245) < 0.01 and abs(100 * unif_patch_sq - 9.2905) < 0.01

    # Part 3B: Honest Variance Attribution on Generalist VLM (4K, 0.07%-area = 76.2x76.2px target)
    side_pro_4k = math.sqrt(0.0007 * w4k * h4k)  # 76.20 px
    sigma_head_gen = 0.055 * w4k  # 211.2 px
    var_head = sigma_head_gen**2
    var_patch = (dx_ap**2) / 12.0
    var_quant = (dx_q**2) / 12.0
    var_tot = var_head + var_patch + var_quant

    hit_gen_full = exact_gauss_unif_hit_2d(
        side_pro_4k, side_pro_4k, sigma_head_gen, sigma_head_gen, dx_ap, dy_ap
    )
    hit_gen_no_patch = exact_gauss_unif_hit_2d(
        side_pro_4k, side_pro_4k, sigma_head_gen, sigma_head_gen, 0.0, 0.0
    )
    hit_patch_only_76 = exact_uniform_hit_2d(side_pro_4k, side_pro_4k, dx_ap, dy_ap)

    print("\n[Part 3B] Variance & Marginal-Ablation Attribution on 4K (0.07% Area = 76.2x76.2px)")
    print(
        f"  Generalist (sigma_head = 5.5%*W = {sigma_head_gen:.1f} px, stride = {dx_ap:.1f} px, quant = {dx_q:.2f} px):\n"
        f"    Variance shares : head = {100*var_head/var_tot:.2f}% | patch = {100*var_patch/var_tot:.2f}% | "
        f"quant = {100*var_quant/var_tot:.4f}%\n"
        f"    Hit probabilities: full = {100*hit_gen_full:.2f}% | setting patch stride->0 = {100*hit_gen_no_patch:.2f}% "
        f"| setting sigma_head->0 (patch-only ceiling) = {100*hit_patch_only_76:.2f}%\n"
        "    -> Coarse generalist collapse (~2.0%) is 97.98% head localization variance; patch aliasing becomes\n"
        "       the binding geometric ceiling once specialist training shrinks sigma_head toward sub-patch scales."
    )
    assert 100 * var_head / var_tot > 97.5

    # Part 3C: Same-Backbone 1-Stage vs 2-Stage Native 1024x1024 Crop + Semantic Crop Recall
    # Hold specialist grounder backbone STRICTLY CONSTANT across 1-Stage and 2-Stage:
    # encoder_max_side = 1024, unmerged 14px ViT stride, encoder-space head sigma_enc = 14.0 enc-px (~1.37% of 1024).
    print(
        "\n[Part 3C] Same-Backbone 1-Stage vs. 2-Stage Native Crop (1024x1024) + Semantic Search Recall"
    )
    print(
        "  Backbone held STRICTLY CONSTANT: 1024px aspect-preserving encoder, 14px patch stride, sigma_enc = 14.0 enc-px.\n"
        "  Evaluates fixed 24x24px icon (ScreenSpot-Pro icon scale) & 48x48px widget (~0.07% area @ 1440p overall scale):"
    )
    print(
        f"  {'Target & Res':<15} | {'Scale':>5} | {'1-Stage (Same Mdl)':>18} | {'Geom P_cap':>10} | "
        f"{'2-Stage Geom (R=1.0)':>20} | {'2-Stage Real (R=0.56)':>21} | {'A11y ID':>7}"
    )
    print("  " + "-" * 110)
    resolutions = [("1080p", 1920.0, 1080.0), ("1440p", 2560.0, 1440.0), ("4K", 3840.0, 2160.0)]
    crop_w = 1024.0
    s_enc = 14.0
    p_stride_enc = 14.0
    r_sem = 0.56

    for box_px, tag in ((24.0, "24px"), (48.0, "48px")):
        one_shot_seq: list[float] = []
        for rname, w_s, h_s in resolutions:
            sc_x, _ = encoder_axis_scales(w_s, h_s, 1024.0, aspect_preserving=True)
            sig_1 = s_enc * sc_x
            str_1 = p_stride_enc * sc_x
            p_1stage = exact_gauss_unif_hit_2d(box_px, box_px, sig_1, sig_1, str_1, str_1)
            one_shot_seq.append(p_1stage)

            cap_box = crop_w - box_px
            p_cap_geom = exact_gauss_unif_hit_2d(cap_box, cap_box, sig_1, sig_1, str_1, str_1)
            p_s2 = exact_gauss_unif_hit_2d(
                box_px, box_px, s_enc, s_enc, p_stride_enc, p_stride_enc
            )
            p_2_oracle = p_cap_geom * p_s2
            p_2_real = r_sem * p_2_oracle
            label_row = f"{tag} @ {rname}"
            print(
                f"  {label_row:<15} | {sc_x:4.2f}x | {100*p_1stage:17.2f}% | {100*p_cap_geom:9.2f}% | "
                f"{100*p_2_oracle:19.2f}% | {100*p_2_real:20.2f}% |  100.0%"
            )
        assert one_shot_seq[0] > one_shot_seq[1] > one_shot_seq[2]
    side_v1_1080 = math.sqrt(0.0201 * 1920.0 * 1080.0)
    sc_1080, _ = encoder_axis_scales(1920.0, 1080.0, 1024.0, aspect_preserving=True)
    p_v1_ctrl = exact_gauss_unif_hit_2d(
        side_v1_1080, side_v1_1080, s_enc * sc_1080, s_enc * sc_1080, 14.0 * sc_1080, 14.0 * sc_1080
    )
    print(
        f"\n  [Negative Control — ScreenSpot v1 2.01% Mean Target Area ({side_v1_1080:.1f}x{side_v1_1080:.1f}px @ 1080p)]:\n"
        f"  Same 1-stage specialist hits {100*p_v1_ctrl:.2f}% without cropping (explaining why v1 masked high-res collapse)."
    )
    assert p_v1_ctrl > 0.99


# =============================================================================
# PROBE 4: True Iterative Byte-Level BPE Bridge Tokens & <eos> Trigger Model
# =============================================================================


class ByteLevelBPE:
    """True iterative rank-priority byte-level BPE tokenizer with GPT-style
    identifier/punctuation pre-tokenization (`[A-Za-z0-9_-]+|[^A-Za-z0-9_-]+`).

    - Base vocabulary ALWAYS retains all 256 single bytes (0..255), including
      ASCII ':', '}', ',', '{', '"', ' ' — never deleting single-byte tokens!
    - Learns ordered pair merges (a, b) -> a+b by corpus frequency within
      pre-tokens and encodes chunks by repeatedly applying the lowest-rank
      (highest-priority) merge.
    """

    PRETOK_RE = re.compile(r"[A-Za-z0-9_-]+|[^A-Za-z0-9_-]+")

    def __init__(self, merges: list[tuple[bytes, bytes]]) -> None:
        self.merges = list(merges)
        self.rank = {pair: idx for idx, pair in enumerate(self.merges)}
        self.vocab: list[bytes] = [bytes([b]) for b in range(256)]
        seen = set(self.vocab)
        for a, b in self.merges:
            ab = a + b
            if ab not in seen:
                self.vocab.append(ab)
                seen.add(ab)

    @classmethod
    def train(cls, corpus: list[tuple[str, int]], num_merges: int) -> ByteLevelBPE:
        """Train iterative byte-level BPE over pre-tokenized byte chunks."""
        chunk_weights: dict[bytes, int] = {}
        for text, weight in corpus:
            for chunk in cls.PRETOK_RE.findall(text):
                cb = chunk.encode("utf-8")
                chunk_weights[cb] = chunk_weights.get(cb, 0) + weight

        seqs: list[tuple[list[bytes], int]] = [
            ([bytes([b]) for b in cb], w) for cb, w in sorted(chunk_weights.items())
        ]
        merges: list[tuple[bytes, bytes]] = []
        for _ in range(num_merges):
            counts: dict[tuple[bytes, bytes], int] = {}
            for tokens, weight in seqs:
                for i in range(len(tokens) - 1):
                    pair = (tokens[i], tokens[i + 1])
                    counts[pair] = counts.get(pair, 0) + weight
            if not counts:
                break
            best_pair = min(counts.keys(), key=lambda p: (-counts[p], p))
            if counts[best_pair] < 2:
                break
            merges.append(best_pair)
            merged_tok = best_pair[0] + best_pair[1]
            new_seqs: list[tuple[list[bytes], int]] = []
            for tokens, weight in seqs:
                out: list[bytes] = []
                i = 0
                while i < len(tokens):
                    if (
                        i < len(tokens) - 1
                        and tokens[i] == best_pair[0]
                        and tokens[i + 1] == best_pair[1]
                    ):
                        out.append(merged_tok)
                        i += 2
                    else:
                        out.append(tokens[i])
                        i += 1
                new_seqs.append((out, weight))
            seqs = new_seqs
        return cls(merges)

    def _encode_chunk(self, chunk_bytes: bytes) -> list[bytes]:
        tokens = [bytes([b]) for b in chunk_bytes]
        while len(tokens) >= 2:
            best_idx = -1
            best_rank = len(self.merges) + 1
            for i in range(len(tokens) - 1):
                r = self.rank.get((tokens[i], tokens[i + 1]))
                if r is not None and r < best_rank:
                    best_rank = r
                    best_idx = i
            if best_idx < 0:
                break
            tokens = (
                tokens[:best_idx]
                + [tokens[best_idx] + tokens[best_idx + 1]]
                + tokens[best_idx + 2 :]
            )
        return tokens

    def encode_bytes(self, text: str) -> list[bytes]:
        out: list[bytes] = []
        for chunk in self.PRETOK_RE.findall(text):
            out.extend(self._encode_chunk(chunk.encode("utf-8")))
        return out


class SimpleJsonStateMachine:
    """Character-level automaton for nested JSON string-value objects:
    OBJ -> '{' WS (STR WS ':' WS (STR | OBJ) (WS ',' WS STR WS ':' WS (STR | OBJ))*)? WS '}'
    """

    @staticmethod
    def step_char(state: tuple[str, int], ch: str) -> tuple[tuple[str, int] | None, bool]:
        mode, depth = state
        if mode == "DONE":
            return None, False
        if mode == "EXPECT_OBJ_OPEN":
            if ch == "{":
                return ("EXPECT_KEY_OR_CLOSE", depth + 1), True
            if ch in " \n":
                return (mode, depth), False
            return None, False
        if mode == "EXPECT_KEY_OR_CLOSE":
            if ch == '"':
                return ("IN_KEY", depth), True
            if ch == "}":
                nxt = ("DONE", 0) if depth == 1 else ("AFTER_VAL", depth - 1)
                return nxt, True
            if ch in " \n":
                return (mode, depth), False
            return None, False
        if mode == "IN_KEY":
            if ch == '"':
                return ("EXPECT_COLON", depth), True
            if ch.isalnum() or ch in "_-":
                return ("IN_KEY", depth), False
            return None, False
        if mode == "EXPECT_COLON":
            if ch == ":":
                return ("EXPECT_VAL", depth), True
            if ch in " \n":
                return (mode, depth), False
            return None, False
        if mode == "EXPECT_VAL":
            if ch == '"':
                return ("IN_VAL", depth), True
            if ch == "{":
                return ("EXPECT_KEY_OR_CLOSE", depth + 1), True
            if ch in " \n":
                return (mode, depth), False
            return None, False
        if mode == "IN_VAL":
            if ch == '"':
                return ("AFTER_VAL", depth), True
            if ch.isalnum() or ch in "_- ":
                return ("IN_VAL", depth), False
            return None, False
        if mode == "AFTER_VAL":
            if ch == ",":
                return ("EXPECT_KEY", depth), True
            if ch == "}":
                nxt = ("DONE", 0) if depth == 1 else ("AFTER_VAL", depth - 1)
                return nxt, True
            if ch in " \n":
                return (mode, depth), False
            return None, False
        if mode == "EXPECT_KEY":
            if ch == '"':
                return ("IN_KEY", depth), True
            if ch in " \n":
                return (mode, depth), False
            return None, False
        return None, False

    @classmethod
    def check_token(
        cls, state: tuple[str, int], tok_bytes: bytes, allow_cross_terminal: bool
    ) -> tuple[bool, tuple[str, int] | None, int]:
        try:
            token = tok_bytes.decode("utf-8")
        except UnicodeDecodeError:
            return False, None, 0
        cur = state
        crossings = 0
        for i, ch in enumerate(token):
            nxt, crossed = cls.step_char(cur, ch)
            if nxt is None:
                return False, None, crossings
            if crossed:
                crossings += 1
            if not allow_cross_terminal and crossings >= 1 and i < len(token) - 1:
                return False, None, crossings
            cur = nxt
        return True, cur, crossings


def run_probe_4() -> None:
    print("\n" + "=" * 92)
    print("PROBE 4 [exact iterative byte-level BPE + trigger-token automaton model]")
    print("Byte-Level BPE Bridge-Token Mass Suppression (k=0) & <eos> Trigger Disjointness")
    print("=" * 92)

    # Train a genuine iterative byte-level BPE tokenizer on mixed JSON + YAML/TS text
    # (all 256 single bytes intact; learns both ': ' / ': "' and '": "' / '", "' / '"}}'!).
    training_corpus = [
        ('{"tool": "get_weather", "args": {"city": "NYC", "units": "metric"}}', 30),
        ('{"tool": "read_file", "args": {"path": "config", "mode": "utf8"}}', 25),
        ('{"name": "search", "params": {"query": "rust", "limit": "ten"}}', 25),
        ('tool: "get_weather"\nargs: {"city": "NYC"}\nmode: "utf8"', 45),
        ("count: 1\nstatus: ok\n", 15),
    ]
    bpe = ByteLevelBPE.train(training_corpus, num_merges=80)

    # Verify all 256 single-byte tokens exist intact in bpe.vocab
    for single in (b":", b"}", b",", b"{", b'"', b" "):
        assert single in bpe.vocab

    payload = '{"tool": "get_weather", "args": {"city": "NYC", "units": "metric"}}'
    canon_bytes = bpe.encode_bytes(payload)
    canon_strs = [b.decode("utf-8") for b in canon_bytes]

    state = ("EXPECT_OBJ_OPEN", 0)
    k0_blocked = []
    for idx, tb in enumerate(canon_bytes):
        ok_k0, _, _ = SimpleJsonStateMachine.check_token(state, tb, allow_cross_terminal=False)
        ok_inf, nxt_state, cross = SimpleJsonStateMachine.check_token(
            state, tb, allow_cross_terminal=True
        )
        assert ok_inf and nxt_state is not None
        if not ok_k0:
            k0_blocked.append((idx, tb.decode("utf-8"), state[0], cross))
        state = nxt_state
    assert state == ("DONE", 0)

    # At EXPECT_COLON (after '"tool"'), inspect ALL valid tokens in real 256-byte+merges BPE vocab!
    st_colon = ("EXPECT_COLON", 1)
    valid_k0_colon = [
        tb.decode("utf-8")
        for tb in bpe.vocab
        if SimpleJsonStateMachine.check_token(st_colon, tb, allow_cross_terminal=False)[0]
        and tb.strip() != b""
    ]
    valid_inf_colon = [
        tb.decode("utf-8")
        for tb in bpe.vocab
        if SimpleJsonStateMachine.check_token(st_colon, tb, allow_cross_terminal=True)[0]
        and tb.strip() != b""
    ]

    # [toy model] Calibrated next-token LM distribution at EXPECT_COLON (after '"tool"'):
    # An LM trained on BPE-tokenized JSON puts >95% mass on canonical merged ': "' / ': {' / ': ',
    # <3% on rare unmerged single-byte ':', and ~1.5% on invalid prose/whitespace drift.
    lm_colon_dist: dict[bytes, float] = {
        b': "': 0.820,
        b': {"': 0.110,
        b": ": 0.042,
        b":": 0.013,  # unmerged single-byte ':' (valid under k=0, but OOD token split!)
        b" ": 0.005,  # bare space (valid under k=0)
        b'"': 0.010,  # syntax error (masked by both)
    }
    assert abs(sum(lm_colon_dist.values()) - 1.0) < 1e-12
    assert set(lm_colon_dist).issubset(set(bpe.vocab))
    mass_k0 = sum(
        p
        for tb, p in lm_colon_dist.items()
        if SimpleJsonStateMachine.check_token(st_colon, tb, allow_cross_terminal=False)[0]
    )
    mass_inf = sum(
        p
        for tb, p in lm_colon_dist.items()
        if SimpleJsonStateMachine.check_token(st_colon, tb, allow_cross_terminal=True)[0]
    )

    print(f"\n[Part 4A] True Iterative Byte-Level BPE (256 Base Bytes Intact + {len(bpe.merges)} Learned Merges)")
    print(f"  Canonical BPE encoding ({len(canon_strs)} tokens): {canon_strs}")
    print(
        f"  Naive k=0 blocks {len(k0_blocked)}/{len(canon_strs)} ({100*len(k0_blocked)/len(canon_strs):.1f}%) "
        f"of canonical BPE tokens (every multi-terminal bridge: {[x[1] for x in k0_blocked]})."
    )
    print(
        f"  Honest EXPECT_COLON check (all 256 single bytes intact — ZERO fake 0-token deadlock):\n"
        f"    Progress-making valid tokens under k=0   : {valid_k0_colon} (single-byte ':' survives!)\n"
        f"    Progress-making valid tokens under k=inf : {valid_inf_colon}\n"
        f"    [toy model] Retained LM probability mass : k=0 retains {100*mass_k0:.1f}% "
        f"(-log Z_t = {-math.log(mass_k0):.2f} nats OOD split penalty!) vs. k=inf retains {100*mass_inf:.1f}% "
        f"(-log Z_t = {-math.log(mass_inf):.3f} nats)."
    )
    assert valid_k0_colon == [":"] and len(valid_inf_colon) > len(valid_k0_colon)
    assert mass_k0 < 0.05 and mass_inf > 0.95

    # Part 4B: Special-Token ID (<eos> vs </think>) vs Surface-Text Delimiter Automaton Analysis
    print("\n[Part 4B] Deferred-Constraining Trigger Taxonomy & In-Writing* (<eos>) Audit")
    eos_id = len(bpe.vocab)
    think_end_id = len(bpe.vocab) + 1

    # Token-stream classification over vocabulary V_text (IDs 0..|V_text|-1) U {eos_id, think_end_id}
    # Verify exact formal disjointness properties rather than hand-picked substring greps:
    text_vocab_strings = {
        tb.decode("utf-8", errors="ignore") for tb in bpe.vocab
    }
    surface_brace_in_text = any("{" in s for s in text_vocab_strings)
    surface_crane_in_text = ("<" in text_vocab_strings)  # '<<' formable in free math/code CoT

    print(
        "  1. Surface-text delimiters (`{`, ````json`, CRANE ASCII `<<` / `>>`, arXiv:2502.09061v4 L326):\n"
        f"     Live inside text vocabulary (brace_in_V={surface_brace_in_text}, '<'_in_V={surface_crane_in_text}) ->\n"
        "     can collide mid-reasoning whenever CoT emits set notation, code snippets, or bitshifts (`1 << 4`).\n"
        f"  2. Reasoning-end special token (`</think>`, ID={think_end_id}, e.g., XGrammar CompileStructuralTag):\n"
        "     Disjoint from text tokens IF matched by special token ID, but absent on non-reasoning instruct\n"
        "     models (Llama-3.1-8B, Gemma-2-9B, Qwen2.5-Coder) and vulnerable if matched as raw surface text.\n"
        "  3. In-Writing* `<eos>` interception (arXiv:2601.07525v2 Sec 6.1 L418-423 & L456):\n"
        f"     Intercepts unique special token `<eos>` (ID={eos_id}, NOT `</think>`!) to activate the grammar:\n"
        "     * Structural invariant: `<eos>` never occurs inside ongoing reasoning on EITHER instruct OR thinking LMs.\n"
        "     * Empirical caveats (Tables 3-5, 9 & App. A.4.2-A.4.3): NOT universally dominant — CRANE (31) beat\n"
        "       In-Writing* (30) on DeepSeek-R1-Llama-8B (GSM-Symbolic Table 9), vanilla Constrained beat In-Writing*\n"
        "       on Qwen3-8B LastLetter (78.4 vs 74.0), Qwen3-4B/3.5-2B Shuffled Obj, and Gemma2-9B DDXPlus, and\n"
        "       In-Writing*'s LastLetter regex applies the same space/hyphen auto-correction as Tam's GPT-4 parser."
    )
    assert eos_id not in range(len(bpe.vocab)) and think_end_id not in range(len(bpe.vocab))
    assert surface_brace_in_text and surface_crane_in_text


def main() -> None:
    print("Deterministic Verification Suite: Structured Outputs, PTC/I-PTC & GUI Grounding (SEED = 20261121)")
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    print("\n" + "=" * 92)
    print("ALL 4 PROBES & NEGATIVE CONTROLS PASSED DETERMINISTIC ASSERTIONS.")
    print("=" * 92)


if __name__ == "__main__":
    main()
