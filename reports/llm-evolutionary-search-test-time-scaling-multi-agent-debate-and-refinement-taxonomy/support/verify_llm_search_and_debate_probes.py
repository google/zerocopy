#!/usr/bin/env python3
"""Self-contained executable verification probes for LLM inference-time search,
multi-agent debate martingales, latent-concept echo chambers, and cross-family
selection gaps.

Requires only the Python 3.10+ standard library; deterministic under fixed seeds.
"""

from __future__ import annotations

import math
import random
from typing import Dict, List, Tuple


def probe_1_choi_martingale_vs_falsifier_drift(
    trials: int = 4000,
    n_agents: int = 5,
    rounds: int = 6,
    seed: int = 20261120,
) -> Dict[str, object]:
    """Verify Choi, Zhu & Li (NeurIPS 2025, Theorem 1 & Theorem 2):
    1. Majority voting over N independent initial draws boosts accuracy above single-agent.
    2. Symmetric Dirichlet-Multinomial peer debate has ZERO expected drift in mean agent
       belief (a martingale: E[p_{i,t} | F_{t-1}] = p_{i,t-1}), while injecting variance
       that causes multi-round consensus accuracy to trail 0-round majority vote.
    3. Adding an asymmetric falsification / counterexample filter (where valid counterexamples
       have higher survival probability than bogus objections) breaks the martingale into a
       strictly positive submartingale.
    """
    rng = random.Random(seed)
    # 3-option multiple choice: option 0 is ground truth (plurality mode 0.46 vs 0.27, 0.27)
    alpha_init = [2.3, 1.35, 1.35]  # sum = 5.0, mean p_true = 0.46

    single_hits = 0
    mv0_hits = 0
    debate_round_hits = [0] * rounds
    debate_mean_p = [0.0] * (rounds + 1)
    falsifier_round_hits = [0] * rounds
    falsifier_mean_p = [0.0] * (rounds + 1)

    def sample_categorical(probs: List[float]) -> int:
        u = rng.random()
        acc = 0.0
        for idx, p in enumerate(probs):
            acc += p
            if u <= acc or idx == len(probs) - 1:
                return idx
        return len(probs) - 1

    for _ in range(trials):
        # Vanilla symmetric Dirichlet-Multinomial debate (complete graph including self)
        alphas = [list(alpha_init) for _ in range(n_agents)]
        debate_mean_p[0] += sum(a[0] / sum(a) for a in alphas) / n_agents

        # Initial round-0 responses
        init_votes = []
        for i in range(n_agents):
            s = sum(alphas[i])
            probs = [x / s for x in alphas[i]]
            init_votes.append(sample_categorical(probs))
        if init_votes[0] == 0:
            single_hits += 1
        counts0 = [init_votes.count(k) for k in range(3)]
        best_c = max(counts0)
        winners0 = [k for k, c in enumerate(counts0) if c == best_c]
        if rng.choice(winners0) == 0:
            mv0_hits += 1

        # Evolve vanilla debate for T rounds
        cur_votes = list(init_votes)
        for r in range(rounds):
            next_alphas = []
            for i in range(n_agents):
                upd = list(alphas[i])
                for j in range(n_agents):
                    upd[cur_votes[j]] += 1.0
                next_alphas.append(upd)
            alphas = next_alphas
            debate_mean_p[r + 1] += sum(a[0] / sum(a) for a in alphas) / n_agents
            cur_votes = []
            for i in range(n_agents):
                s = sum(alphas[i])
                cur_votes.append(sample_categorical([x / s for x in alphas[i]]))
            cnt = [cur_votes.count(k) for k in range(3)]
            mx = max(cnt)
            win = [k for k, c in enumerate(cnt) if c == mx]
            if rng.choice(win) == 0:
                debate_round_hits[r] += 1

        # Asymmetric falsifier-gated debate: an agent adopting a candidate must survive
        # a concrete falsification check (wrong candidates refuted with prob 0.55; true
        # candidate falsely refuted with prob 0.08).
        f_alphas = [list(alpha_init) for _ in range(n_agents)]
        falsifier_mean_p[0] += sum(a[0] / sum(a) for a in f_alphas) / n_agents
        f_votes = list(init_votes)
        for r in range(rounds):
            next_f = []
            for i in range(n_agents):
                upd = list(f_alphas[i])
                for j in range(n_agents):
                    cand = f_votes[j]
                    refute_prob = 0.08 if cand == 0 else 0.55
                    if rng.random() >= refute_prob:
                        upd[cand] += 1.0
                next_f.append(upd)
            f_alphas = next_f
            falsifier_mean_p[r + 1] += sum(a[0] / sum(a) for a in f_alphas) / n_agents
            f_votes = []
            for i in range(n_agents):
                s = sum(f_alphas[i])
                f_votes.append(sample_categorical([x / s for x in f_alphas[i]]))
            cnt = [f_votes.count(k) for k in range(3)]
            mx = max(cnt)
            win = [k for k, c in enumerate(cnt) if c == mx]
            if rng.choice(win) == 0:
                falsifier_round_hits[r] += 1

    return {
        "single_agent_acc": round(single_hits / trials, 4),
        "majority_vote_r0_acc": round(mv0_hits / trials, 4),
        "vanilla_debate_mean_belief": [round(x / trials, 4) for x in debate_mean_p],
        "vanilla_debate_vote_acc_by_round": [round(x / trials, 4) for x in debate_round_hits],
        "falsifier_debate_mean_belief": [round(x / trials, 4) for x in falsifier_mean_p],
        "falsifier_debate_vote_acc_by_round": [round(x / trials, 4) for x in falsifier_round_hits],
    }


def probe_2_estornell_liu_echo_chamber_and_misconception() -> Dict[str, object]:
    """Verify Estornell & Liu (NeurIPS 2024, Lemma 4.2 & Theorems 5.1, 5.2, 5.4):
    Under conditional independence given latent concept theta in {theta_true, theta_misc},
    compute exact posterior weight on theta_true as homogeneous/majority misconception count m grows.
    """
    # Solo prior P(theta | x, phi): slight misconception bias (0.48 true vs 0.52 misconception)
    # vs slight truth bias (0.55 true vs 0.45 misconception) when majority m holds misconception.
    # Likelihood of typical misconception utterance z_misc under theta_misc is 0.80 vs 0.25 under theta_true.
    results = {}
    for scenario, p_true_solo in [("slight_truth_prior_0.55", 0.55), ("shared_misconception_prior_0.45", 0.45)]:
        p_misc_solo = 1.0 - p_true_solo
        curve = {}
        # Suppose 1 dissenting agent emits a truth-aligned utterance (0.80 under true, 0.25 under misc)
        # while m agents emit misconception-aligned utterances (0.25 under true, 0.80 under misc).
        for m in [0, 1, 2, 3, 5, 8]:
            w_true = p_true_solo * (0.80 ** 1) * (0.25 ** m)
            w_misc = p_misc_solo * (0.25 ** 1) * (0.80 ** m)
            post_true = w_true / (w_true + w_misc)
            curve[f"m={m}"] = round(post_true, 6)
        results[scenario] = curve
    return results


def probe_3_brown_monkeys_verifier_gap(
    trials: int = 2000,
    seed: int = 20261120,
) -> Dict[str, Dict[str, float]]:
    """Verify Brown et al. (2024, 'Large Language Monkeys') coverage vs selection gap:
    Suppose rare breakthrough design occurs with p_good = 0.03, a seductive misconception
    occurs with p_misc = 0.22, and fragmented mediocre answers split remaining mass across
    15 bins (0.05 each). Compare:
    - Oracle Verifier (pass@k coverage): 1 - (1 - p_good)^k
    - Majority Vote accuracy as k scales from 1 to 512
    - Noisy LLM Judge / Reward Model (scores good ~ N(0.78, 0.14^2), misc ~ N(0.74, 0.14^2),
      mediocre ~ N(0.50, 0.14^2)) Best-of-k accuracy as k scales!
     Notice how Best-of-k under a noisy proxy peaks at moderate k and then DEGRADES (Goodhart
    winner's curse: 7.3x more misconception draws produce extreme upper-tail noise!).
    """
    rng = random.Random(seed)
    p_good = 0.03
    p_misc = 0.22
    n_med = 15
    p_med_each = (1.0 - p_good - p_misc) / n_med  # 0.05

    ks = [1, 4, 16, 64, 256, 512]
    summary: Dict[str, Dict[str, float]] = {}

    for k in ks:
        oracle_hits = 0
        mv_hits = 0
        rm_hits = 0
        for _ in range(trials):
            counts = [0] * (2 + n_med)  # 0=good, 1=misc, 2..16=mediocre
            best_rm_score = -1e9
            best_rm_cls = -1
            for _s in range(k):
                u = rng.random()
                if u < p_good:
                    cls = 0
                    mu = 0.78
                elif u < p_good + p_misc:
                    cls = 1
                    mu = 0.74
                else:
                    idx = min(int((u - p_good - p_misc) / p_med_each), n_med - 1)
                    cls = 2 + idx
                    mu = 0.50
                counts[cls] += 1
                score = rng.gauss(mu, 0.14)
                if score > best_rm_score:
                    best_rm_score = score
                    best_rm_cls = cls

            if counts[0] > 0:
                oracle_hits += 1
            mx = max(counts)
            winners = [idx for idx, c in enumerate(counts) if c == mx]
            if rng.choice(winners) == 0:
                mv_hits += 1
            if best_rm_cls == 0:
                rm_hits += 1

        summary[f"k={k}"] = {
            "oracle_pass_at_k": round(oracle_hits / trials, 4),
            "majority_vote_acc": round(mv_hits / trials, 4),
            "noisy_rm_best_of_k_acc": round(rm_hits / trials, 4),
        }
    return summary


def probe_4_capability_asymmetric_sycophancy(
    trials: int = 5000,
    seed: int = 20261120,
) -> Dict[str, float]:
    """Verify Wynn, Satija & Hadfield (2025) capability-asymmetric debate degradation:
    2 strong agents (p_strong = 0.82) + 1 weak agent (p_weak = 0.38, concentrating errors
    on a persuasive common misconception). Compare pre-debate majority vote vs 2-round
    unmoderated peer debate with empirically realistic conformity/sycophancy flip rates.
    """
    rng = random.Random(seed)
    p_s = 0.82
    p_w = 0.38

    mv_pre = 0
    mv_post = 0
    strong_c2i = 0
    strong_c_init = 0

    for _ in range(trials):
        # Binary indicator of holding correct answer (1) vs shared misconception (0)
        s1 = 1 if rng.random() < p_s else 0
        s2 = 1 if rng.random() < p_s else 0
        w1 = 1 if rng.random() < p_w else 0
        state = [s1, s2, w1]
        if sum(state) >= 2:
            mv_pre += 1
        strong_c_init += s1 + s2

        for _r in range(2):
            nxt = list(state)
            for idx in range(3):
                peers = [state[j] for j in range(3) if j != idx]
                agree = sum(1 for p in peers if p == state[idx])
                is_strong = idx < 2
                if state[idx] == 1:
                    # Correct -> Incorrect sycophancy/conformity flip rate
                    if agree == 0:
                        flip_p = 0.42 if is_strong else 0.70
                    elif agree == 1:
                        flip_p = 0.16 if is_strong else 0.35
                    else:
                        flip_p = 0.02
                else:
                    # Incorrect -> Correct correction rate without external verifier
                    if agree == 0:
                        flip_p = 0.38 if is_strong else 0.22
                    elif agree == 1:
                        flip_p = 0.08 if is_strong else 0.06
                    else:
                        flip_p = 0.01
                if rng.random() < flip_p:
                    nxt[idx] = 1 - state[idx]
            state = nxt

        if s1 == 1 and state[0] == 0:
            strong_c2i += 1
        if s2 == 1 and state[1] == 0:
            strong_c2i += 1
        if sum(state) >= 2:
            mv_post += 1

    return {
        "pre_debate_majority_acc": round(mv_pre / trials, 4),
        "post_2round_debate_acc": round(mv_post / trials, 4),
        "net_debate_delta": round((mv_post - mv_pre) / trials, 4),
        "strong_correct_to_incorrect_rate": round(strong_c2i / max(strong_c_init, 1), 4),
    }


def main() -> None:
    p1 = probe_1_choi_martingale_vs_falsifier_drift()
    print("=== Probe 1: Choi-Zhu-Li Martingale vs Falsifier-Gated Submartingale ===")
    for k, v in p1.items():
        print(f"  {k}: {v}")

    p2 = probe_2_estornell_liu_echo_chamber_and_misconception()
    print("\n=== Probe 2: Estornell-Liu Tyranny of Majority & Misconception Skew ===")
    for k, v in p2.items():
        print(f"  {k}: {v}")

    p3 = probe_3_brown_monkeys_verifier_gap()
    print("\n=== Probe 3: Brown et al. Pass@k Coverage vs Noisy Judge Winner's Curse ===")
    for k, v in p3.items():
        print(f"  {k:6s} -> {v}")

    p4 = probe_4_capability_asymmetric_sycophancy()
    print("\n=== Probe 4: Capability-Asymmetric Debate (2 Strong + 1 Weak) ===")
    for k, v in p4.items():
        print(f"  {k}: {v}")


if __name__ == "__main__":
    main()
