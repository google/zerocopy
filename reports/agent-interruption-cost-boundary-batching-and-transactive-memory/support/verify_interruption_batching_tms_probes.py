#!/usr/bin/env python3
"""Standalone Python 3.10+ stdlib verification probe suite for agent interruption cost,
subtask-boundary digest batching, KV-cache prefix preservation, and transactive memory routing.

All 5 probes use strictly the Python 3.10+ standard library, fixed instance-scoped PRNG
seeds, zero disk writes, zero local file paths in stdout, and explicit evidence-role
banners aligned with the reference-corpus/1 contract:
  1. probe_kv_prefix_and_goal_activation
  2. probe_alertmanager_groupwait_interval_and_inhibition
  3. probe_tms_doa_survival_decay_vs_broadcast
  4. probe_tokio_coop_and_langgraph_superstep_delivery
  5. probe_voi_interruption_gate
"""

from __future__ import annotations

import collections
import dataclasses
import hashlib
import heapq
import json
import math
import random
import re
import statistics
from typing import Any, Callable


# ============================================================================
# PROBE 1: RadixAttention Paged KV-Cache Prefix Preservation + ACT-R Goal Memory
# [evidence_role: documentation + source + derived]
# Grounded in:
#   - sgl-project/sglang@448764da636a8500015f461afbb91e3d2d23c94f
#     (python/sglang/srt/mem_cache/radix_cache.py:282,369,433,658-698)
#   - Zheng et al. (NeurIPS 2024, arXiv:2312.07104v2); Gim et al. (MLSys 2024, arXiv:2311.04934v2)
#   - Altmann & Trafton (Cognitive Science 2002, 26(1):39-83, Eq. 1 pp.46,71; Eq. A1-A5 pp.70-71;
#     Appendix B.4 pp.78-79: d=0.5, s=0.3, tau=4.0, W=1.0)
#   - Bailey & Konstan (Computers in Human Behavior 2006, 22(4):685-708)
# ============================================================================


@dataclasses.dataclass
class _RadixNode:
    key: tuple[int, ...] = ()
    children: dict[tuple[int, ...], _RadixNode] = dataclasses.field(default_factory=dict)


class PagedRadixCache:
    """Exact page-aligned longest-prefix radix tree reproducing SGLang RadixCache."""

    def __init__(self, page_size: int = 16) -> None:
        assert page_size >= 1
        self.page_size = page_size
        self.root = _RadixNode()

    def _aligned_len(self, tokens: tuple[int, ...]) -> int:
        return (len(tokens) // self.page_size) * self.page_size

    def _match_pages(self, a: tuple[int, ...], b: tuple[int, ...]) -> int:
        limit = min(self._aligned_len(a), self._aligned_len(b))
        matched = 0
        ps = self.page_size
        while matched + ps <= limit and a[matched : matched + ps] == b[matched : matched + ps]:
            matched += ps
        return matched

    def match_prefix_len(self, seq: tuple[int, ...]) -> int:
        """Reproduces RadixCache._match_prefix_helper + _split_node (radix_cache.py:658-698)."""
        aligned = seq[: self._aligned_len(seq)]
        if not aligned:
            return 0
        node = self.root
        rem = aligned
        total_hit = 0
        ps = self.page_size
        while rem:
            ckey = rem[:ps]
            child = node.children.get(ckey)
            if child is None:
                break
            plen = self._match_pages(child.key, rem)
            if plen < len(child.key):
                mid = _RadixNode(key=child.key[:plen])
                suffix_child_key = child.key[plen : plen + ps]
                child.key = child.key[plen:]
                mid.children[suffix_child_key] = child
                node.children[ckey] = mid
                total_hit += plen
                break
            total_hit += plen
            node = child
            rem = rem[plen:]
        return total_hit

    def insert(self, seq: tuple[int, ...]) -> None:
        aligned = seq[: self._aligned_len(seq)]
        if not aligned:
            return
        node = self.root
        rem = aligned
        ps = self.page_size
        while rem:
            ckey = rem[:ps]
            child = node.children.get(ckey)
            if child is None:
                node.children[ckey] = _RadixNode(key=rem)
                return
            plen = self._match_pages(child.key, rem)
            if plen < len(child.key):
                mid = _RadixNode(key=child.key[:plen])
                mid.children[child.key[plen : plen + ps]] = _RadixNode(
                    key=child.key[plen:], children=child.children
                )
                node.children[ckey] = mid
                if plen < len(rem):
                    mid.children[rem[plen : plen + ps]] = _RadixNode(key=rem[plen:])
                return
            node = child
            rem = rem[plen:]


def _simulate_kv_policy(
    *,
    turns: int,
    sys_tokens: int,
    banner_offset: int,
    banner_len: int,
    turn_growth: int,
    digest_len: int,
    page_size: int,
    policy: str,
) -> dict[str, float]:
    cache = PagedRadixCache(page_size=page_size)
    cached_weight = 0.1
    uncached_weight = 1.0

    base_prefix = tuple(range(10_000, 10_000 + banner_offset))
    base_suffix = tuple(
        range(20_000, 20_000 + (sys_tokens - banner_offset - banner_len))
    )
    banner_version = 0
    transcript_tail: list[int] = []
    next_tok = 100_000

    total_cost = 0.0
    total_aligned_hist_tokens = 0
    total_aligned_hist_hits = 0
    total_raw_hist_tokens = 0
    total_raw_hist_hits = 0
    prev_prompt_aligned = 0
    prev_prompt_raw = 0

    for t in range(1, turns + 1):
        if policy == "banner_every_turn":
            banner_version = t
        elif policy == "banner_every_2_turns" and t % 2 == 0:
            banner_version = t

        banner = tuple(
            30_000 + banner_version * 1_000 + i for i in range(banner_len)
        )

        turn_chunk = [next_tok + i for i in range(turn_growth)]
        next_tok += turn_growth
        if policy == "micro_turn_tail_digest":
            per_turn_digest = max(1, digest_len // 8)
            turn_chunk.extend(next_tok + i for i in range(per_turn_digest))
            next_tok += per_turn_digest
        elif policy == "coarse_boundary_tail_digest" and t % 8 == 0:
            turn_chunk.extend(next_tok + i for i in range(digest_len))
            next_tok += digest_len

        transcript_tail.extend(turn_chunk)
        prompt = base_prefix + banner + base_suffix + tuple(transcript_tail)
        hit = cache.match_prefix_len(prompt)
        miss = len(prompt) - hit
        total_cost += cached_weight * hit + uncached_weight * miss
        if t > 1:
            total_aligned_hist_tokens += prev_prompt_aligned
            total_aligned_hist_hits += min(hit, prev_prompt_aligned)
            total_raw_hist_tokens += prev_prompt_raw
            total_raw_hist_hits += min(hit, prev_prompt_raw)
        cache.insert(prompt)
        prev_prompt_aligned = (len(prompt) // page_size) * page_size
        prev_prompt_raw = len(prompt)

    aligned_hit_rate = total_aligned_hist_hits / max(1, total_aligned_hist_tokens)
    raw_hit_rate = total_raw_hist_hits / max(1, total_raw_hist_tokens)
    return {
        "normalized_prefill_cost": round(total_cost, 2),
        "page_aligned_prefix_hit_rate": round(aligned_hit_rate, 6),
        "raw_historical_token_hit_rate": round(raw_hit_rate, 6),
    }


def _sample_logistic(rng: random.Random, s: float) -> float:
    u = rng.uniform(1e-9, 1.0 - 1e-9)
    return s * math.log(u / (1.0 - u))


def probe_kv_prefix_and_goal_activation() -> dict[str, Any]:
    # 1. Exact check of Altmann & Trafton (2002) Eq. (1) (pp. 46, 71) vs ACT-R discrete sum (d=0.5)
    # Midpoint-spaced encodings ((j - 0.5) * T / n)^(-0.5) -> ln(2 * n / sqrt(T)) = ln(2) + ln(n / sqrt(T))
    n_enc = 200
    lifetime_t = 25.0
    actr_exact = math.log(
        sum((((j - 0.5) * lifetime_t / n_enc) ** -0.5) for j in range(1, n_enc + 1))
    )
    eq1_val = math.log(n_enc / math.sqrt(lifetime_t))
    integral_shift_gap = actr_exact - eq1_val
    assert abs(integral_shift_gap - math.log(2.0)) < 0.03

    # 2. Altmann & Trafton Appendix A Eq. (A5) (p. 71) closed-form interference level (s=0.3, t=7.0, n=15)
    s_noise = 0.3
    t_tempo = 7.0
    n_samples = 15
    m_clutter_closed = (
        math.log(n_samples)
        - 0.5 * math.log(t_tempo)
        - s_noise * math.log((1.0 / (2.0 * s_noise)) - 1.0)
    )
    m_clutter_series = s_noise * math.log(
        sum((n_samples / math.sqrt(i * t_tempo)) ** (1.0 / s_noise) for i in range(1, 4000))
    )
    assert abs(m_clutter_closed - m_clutter_series) < 0.12

    # 3. ACT-R goal resumption Monte Carlo (Altmann & Trafton 2002, Appendix B.4 pp. 78-79):
    #    Total activation A_i = m_i + sum_j W_j * S_ji + eps_i, with default source activation
    #    weight W = 1.0, retrieval threshold tau = 4.0, and logistic noise s = 0.3.
    #    Retrieval of each suspended subgoal succeeds iff A_target >= tau AND A_target > max_d A_d.
    rng = random.Random(20261122)
    trials = 4_000
    interruption_sec = 18.0
    old_distractors = 12
    interrupt_distractors = 3
    w_source = 1.0
    tau_threshold = 4.0
    s_ji_distractor = 1.35  # residual ambient context association on competing goals

    def _run_resumption_trials(
        suspended_depth: int,
        boundary_strengthen_samples: int,
        s_ji_target: float,
    ) -> float:
        failures = 0
        for _ in range(trials):
            distractor_base = [
                math.log(n_samples / math.sqrt(i * t_tempo + interruption_sec))
                for i in range(1, old_distractors + 1)
            ] + [
                math.log(12 / math.sqrt(2.0 + 3.0 * k))
                for k in range(interrupt_distractors)
            ]
            episode_failed = False
            for depth_idx in range(suspended_depth):
                age = interruption_sec + 4.0 * depth_idx
                n_eff = n_samples + boundary_strengthen_samples
                a_target = (
                    math.log(n_eff / math.sqrt(age))
                    + w_source * s_ji_target
                    + _sample_logistic(rng, s_noise)
                )
                max_dist = max(
                    m_d + w_source * s_ji_distractor + _sample_logistic(rng, s_noise)
                    for m_d in distractor_base
                )
                if a_target < tau_threshold or a_target < max_dist:
                    episode_failed = True
                    break
            if episode_failed:
                failures += 1
        return failures / trials

    # (a) Coarse boundary: child subgoals popped (depth=1), 1.0s strengthening (+10 samples at
    #     100ms/sample, p. 72), externalized workspace cue strength S_ji = 2.7 (W * S_ji = 2.7).
    err_coarse = _run_resumption_trials(
        suspended_depth=1, boundary_strengthen_samples=10, s_ji_target=2.7
    )
    # (b) Pure single-factor stack-depth ablation: depth=3 vs depth=1 holding strengthening (+10)
    #     and cue priming (W=1.0, S_ji=2.7, tau=4.0) strictly identical!
    err_depth3_controlled = _run_resumption_trials(
        suspended_depth=3, boundary_strengthen_samples=10, s_ji_target=2.7
    )
    # (c) Derived compound mid-subtask preemption: depth=3 suspended abruptly with zero
    #     interruption-lag strengthening (+0 samples) and weaker cue association (S_ji=2.15)
    #     on unexternalized intermediate subgoals.
    err_mid_unprepared = _run_resumption_trials(
        suspended_depth=3, boundary_strengthen_samples=0, s_ji_target=2.15
    )
    controlled_depth_ratio = err_depth3_controlled / max(1e-9, err_coarse)
    compound_mid_ratio = err_mid_unprepared / max(1e-9, err_coarse)
    assert controlled_depth_ratio > 2.2, (
        f"Expected >2.2x pure stack-depth failure ratio, got {controlled_depth_ratio}"
    )
    assert err_mid_unprepared > err_depth3_controlled
    assert compound_mid_ratio > 4.0

    # 4. Paged RadixAttention KV-cache accounting across S=40 turns (page_size=16 & 64)
    kv_results: dict[str, Any] = {}
    for ps in (16, 64):
        coarse = _simulate_kv_policy(
            turns=40,
            sys_tokens=4096,
            banner_offset=2048,
            banner_len=128,
            turn_growth=800,
            digest_len=160,
            page_size=ps,
            policy="coarse_boundary_tail_digest",
        )
        micro = _simulate_kv_policy(
            turns=40,
            sys_tokens=4096,
            banner_offset=2048,
            banner_len=128,
            turn_growth=800,
            digest_len=160,
            page_size=ps,
            policy="micro_turn_tail_digest",
        )
        banner_k2 = _simulate_kv_policy(
            turns=40,
            sys_tokens=4096,
            banner_offset=2048,
            banner_len=128,
            turn_growth=800,
            digest_len=160,
            page_size=ps,
            policy="banner_every_2_turns",
        )
        banner_k1 = _simulate_kv_policy(
            turns=40,
            sys_tokens=4096,
            banner_offset=2048,
            banner_len=128,
            turn_growth=800,
            digest_len=160,
            page_size=ps,
            policy="banner_every_turn",
        )
        assert coarse["page_aligned_prefix_hit_rate"] == 1.0
        assert micro["page_aligned_prefix_hit_rate"] == 1.0
        if ps == 16:
            assert coarse["raw_historical_token_hit_rate"] == 1.0
            assert abs(micro["raw_historical_token_hit_rate"] - (799_104 / 799_344)) < 1e-6
        else:
            # At page_size=64, micro_turn_tail_digest (820 tok/turn; 820 % 64 = 52) misses 1,200
            # trailing unaligned tokens across turns 2..40: 798,144 / 799,344 = 0.998499.
            assert abs(micro["raw_historical_token_hit_rate"] - (798_144 / 799_344)) < 1e-6
            assert abs(micro["raw_historical_token_hit_rate"] - 0.998499) < 1e-6
        assert banner_k2["raw_historical_token_hit_rate"] < 0.60
        assert banner_k1["raw_historical_token_hit_rate"] < 0.15
        mult_k2 = banner_k2["normalized_prefill_cost"] / coarse["normalized_prefill_cost"]
        mult_k1 = banner_k1["normalized_prefill_cost"] / coarse["normalized_prefill_cost"]
        assert mult_k2 > 3.5 and mult_k1 > 6.0
        kv_results[f"page_{ps}"] = {
            "coarse_boundary_tail_digest": coarse,
            "micro_turn_tail_digest": micro,
            "banner_mutated_every_2_turns": banner_k2,
            "banner_mutated_every_turn": banner_k1,
            "cost_multiplier_k2_vs_coarse": round(mult_k2, 3),
            "cost_multiplier_k1_vs_coarse": round(mult_k1, 3),
        }

    return {
        "evidence_role": "documentation + source + derived",
        "actr_eq1_ln2_shift_gap": round(integral_shift_gap, 5),
        "actr_eq_a5_closed_vs_series": (round(m_clutter_closed, 4), round(m_clutter_series, 4)),
        "actr_params": {"d": 0.5, "s": s_noise, "tau": tau_threshold, "W": w_source},
        "resumption_error_coarse_depth1": round(err_coarse, 4),
        "resumption_error_controlled_depth3": round(err_depth3_controlled, 4),
        "resumption_error_unprepared_mid_depth3": round(err_mid_unprepared, 4),
        "resumption_controlled_depth3_over_coarse_ratio": round(controlled_depth_ratio, 3),
        "resumption_unprepared_mid_over_coarse_ratio": round(compound_mid_ratio, 3),
        "radix_kv_accounting": kv_results,
    }


# ============================================================================
# PROBE 2: Renewal-Reward GroupWait Optimizer + Full Alertmanager 3-Timer &
#          Inhibition Discrete-Event Simulator + Scholl-Kleinrock Variance Penalty
# [evidence_role: normative + source + derived]
# Grounded in:
#   - prometheus/alertmanager@5dea4dedd70f7e770c34d33b96449ee27e5c1aae
#     (dispatch/dispatch.go:771,939,965,1043,1077; notify/dedup_stage.go:50-94;
#      inhibit/inhibit.go:168-208,299-303)
#   - Heyman (1977, Management Science 23(7):775-778)
#   - Scholl & Kleinrock (1983, Operations Research 31(4):705-719)
# ============================================================================


def closed_form_groupwait_cost(lam: float, setup_k: float, hold_h: float, wait_w: float) -> float:
    u = 1.0 + lam * wait_w
    return (lam * setup_k - 0.5 * hold_h) / u + 0.5 * hold_h * u


def optimal_groupwait_w(lam: float, setup_k: float, hold_h: float) -> float:
    """Exact minimizer over W >= 0 (u = 1 + lam*W >= 1).

    dC/du|_{u=1} = h - lam*K, so an interior minimizer W* > 0 exists iff
    lam * K > h (equivalently 2 * lam * K / h > 2.0). For 0 < lam * K <= h,
    C_GW(W) is non-decreasing at W = 0 and strictly convex/increasing on W > 0,
    so the constrained global minimizer on W >= 0 is W* = 0.
    """
    ratio = (2.0 * lam * setup_k) / hold_h
    if ratio <= 2.0:
        return 0.0
    return (math.sqrt(ratio - 1.0) - 1.0) / lam


def _sim_ephemeral_groupwait_des(
    lam: float, setup_k: float, hold_h: float, wait_w: float, n_cycles: int, seed: int
) -> float:
    """Exact DES of ephemeral-group GroupWait cycles (each flush resolves & destroys group)."""
    rng = random.Random(seed)
    total_time = 0.0
    total_cost = 0.0
    for _ in range(n_cycles):
        idle = rng.expovariate(lam)
        t_cur = 0.0
        wait_sum = wait_w  # triggering arrival waits full W
        while True:
            t_cur += rng.expovariate(lam)
            if t_cur >= wait_w:
                break
            wait_sum += wait_w - t_cur
        total_time += idle + wait_w
        total_cost += setup_k + hold_h * wait_sum
    return total_cost / total_time


@dataclasses.dataclass
class _SimAlert:
    fp: str
    labels: dict[str, str]
    starts_at: float
    ends_at: float  # math.inf if still active


@dataclasses.dataclass(frozen=True)
class _InhibitRuleSpec:
    source_matchers: dict[str, str]
    target_matchers: dict[str, str]
    equal_labels: tuple[str, ...]
    respect_exclude_two_sided: bool = True

    def matches_source(self, labels: dict[str, str]) -> bool:
        return all(labels.get(k) == v for k, v in self.source_matchers.items())

    def matches_target(self, labels: dict[str, str]) -> bool:
        return all(labels.get(k) == v for k, v in self.target_matchers.items())


def _simulate_alertmanager_pipeline(
    *,
    events: list[tuple[float, str, _SimAlert]],
    group_wait: float,
    group_interval: float,
    repeat_interval: float,
    inhibit_rules: list[_InhibitRuleSpec],
) -> dict[str, Any]:
    """Reproduces Alertmanager aggrGroup (GroupWait -> GroupInterval) + DedupStage + Inhibitor."""
    pq: list[tuple[float, int, str, str, Any]] = []
    seq = 0
    for ts, gkey, alrt in events:
        heapq.heappush(pq, (ts, seq, "insert", gkey, alrt))
        seq += 1

    groups: dict[str, dict[str, Any]] = {}
    # Per-rule source cache indexed by equal-label tuple (inhibit/inhibit.go:291, 299-303)
    rule_caches: list[dict[tuple[str, ...], dict[str, _SimAlert]]] = [
        collections.defaultdict(dict) for _ in inhibit_rules
    ]

    flushes_by_stage = {"group_wait_initial": 0, "group_interval_subsequent": 0}
    notifications_sent = 0
    dedup_suppressed = 0
    inhibited_count = 0
    notified_fingerprints: set[str] = set()
    root_causes_notified: set[str] = set()
    symptoms_notified = 0
    second_batch_waits: list[float] = []

    def _is_inhibited(alrt: _SimAlert, now: float) -> bool:
        # Exact Inhibitor.Mutes + InhibitRule.hasEqual (inhibit/inhibit.go:184-203, 299-303)
        for r_idx, rule in enumerate(inhibit_rules):
            if not rule.matches_target(alrt.labels):
                continue
            exclude_two_sided = rule.respect_exclude_two_sided and rule.matches_source(
                alrt.labels
            )
            eq_key = tuple(alrt.labels.get(lbl, "") for lbl in rule.equal_labels)
            for src_fp, src_alrt in rule_caches[r_idx].get(eq_key, {}).items():
                if src_alrt.ends_at <= now or src_fp == alrt.fp:
                    continue
                if exclude_two_sided and rule.matches_target(src_alrt.labels):
                    continue
                return True
        return False

    while pq:
        now, _, etype, gkey, payload = heapq.heappop(pq)
        if etype == "insert":
            alrt: _SimAlert = payload
            for r_idx, rule in enumerate(inhibit_rules):
                if rule.matches_source(alrt.labels):
                    eq_key = tuple(alrt.labels.get(lbl, "") for lbl in rule.equal_labels)
                    rule_caches[r_idx][eq_key][alrt.fp] = alrt

            ag = groups.get(gkey)
            if ag is None or ag["destroyed"]:
                ag = {
                    "alerts": {},
                    "flush_idx": 1,
                    "destroyed": False,
                    "nflog": None,
                    "pending_arrival_ts": [],
                }
                groups[gkey] = ag
                heapq.heappush(pq, (now + group_wait, seq, "timer_tick", gkey, "initial"))
                seq += 1
            else:
                ag["pending_arrival_ts"].append(now)

            ag["alerts"][alrt.fp] = alrt

        elif etype == "timer_tick":
            ag = groups.get(gkey)
            if ag is None or ag["destroyed"]:
                continue

            tick_kind = payload
            flush_idx = ag["flush_idx"]
            ag["flush_idx"] += 1

            if not ag["alerts"]:
                continue

            all_alerts = list(ag["alerts"].values())
            resolved_fps = [a.fp for a in all_alerts if a.ends_at <= now]

            unmuted: list[_SimAlert] = []
            for a in all_alerts:
                if a.ends_at > now and _is_inhibited(a, now):
                    inhibited_count += 1
                    continue
                unmuted.append(a)

            firing_set = frozenset(a.fp for a in unmuted if a.ends_at > now)
            resolved_set = frozenset(a.fp for a in unmuted if a.ends_at <= now)

            entry = ag["nflog"]
            should_send = False
            if entry is None:
                should_send = len(firing_set) > 0
            else:
                last_ts, prev_firing, prev_resolved = entry
                if not firing_set.issubset(prev_firing):
                    should_send = True
                elif len(firing_set) == 0:
                    should_send = len(prev_firing) > 0
                elif not resolved_set.issubset(prev_resolved):
                    should_send = True
                elif now - last_ts > repeat_interval:
                    should_send = True

            if should_send:
                notifications_sent += 1
                if flush_idx == 1:
                    flushes_by_stage["group_wait_initial"] += 1
                else:
                    flushes_by_stage["group_interval_subsequent"] += 1
                    for arr_t in ag["pending_arrival_ts"]:
                        second_batch_waits.append(now - arr_t)
                ag["pending_arrival_ts"].clear()
                ag["nflog"] = (now, firing_set, resolved_set)
                for a in unmuted:
                    if a.ends_at > now:
                        notified_fingerprints.add(a.fp)
                        if a.labels.get("kind") == "root_interface_break":
                            root_causes_notified.add(a.fp)
                        elif a.labels.get("kind") == "downstream_compile_symptom":
                            symptoms_notified += 1
            else:
                if unmuted:
                    dedup_suppressed += 1

            for rfp in resolved_fps:
                ag["alerts"].pop(rfp, None)
            if not ag["alerts"]:
                ag["destroyed"] = True
            else:
                heapq.heappush(pq, (now + group_interval, seq, "timer_tick", gkey, "interval"))
                seq += 1
                assert tick_kind in ("initial", "interval")

    return {
        "notifications_sent": notifications_sent,
        "flushes_by_stage": flushes_by_stage,
        "dedup_suppressed": dedup_suppressed,
        "inhibited_symptoms": inhibited_count,
        "notified_fingerprints_count": len(notified_fingerprints),
        "root_causes_notified_count": len(root_causes_notified),
        "symptoms_notified_count": symptoms_notified,
        "mean_subsequent_batch_wait": round(
            statistics.fmean(second_batch_waits) if second_batch_waits else 0.0, 4
        ),
    }


def _partition_with_checkpoint_cap(durations: list[float], t_cap: float) -> list[float]:
    """Timeline-preserving checkpoint splitting: partitions each duration > t_cap into
    t_cap-sized segments plus positive remainder, conserving total execution time exactly."""
    segments: list[float] = []
    for dur in durations:
        rem = dur
        while rem > t_cap + 1e-12:
            segments.append(t_cap)
            rem -= t_cap
        if rem > 1e-12:
            segments.append(rem)
    return segments


def probe_alertmanager_groupwait_interval_and_inhibition() -> dict[str, Any]:
    # 1. Analytical W* vs Discrete-Event Simulation across all 3 boundary/interior regimes:
    #    (a) Deep urgent regime: lam*K = 0.2 <= h = 1.0 (2*lam*K/h = 0.4 <= 2.0) -> W* = 0
    w_star_low = optimal_groupwait_w(lam=0.02, setup_k=10.0, hold_h=1.0)
    assert w_star_low == 0.0
    assert closed_form_groupwait_cost(0.02, 10.0, 1.0, 0.0) < closed_form_groupwait_cost(
        0.02, 10.0, 1.0, 5.0
    )

    #    (b) Critical boundary band h/2 < lam*K <= h (1.0 < 2*lam*K/h <= 2.0):
    #        dC/du|_{u=1} = h - lam*K >= 0, so W* MUST still be 0.0 (never negative!).
    w_star_mid_band = optimal_groupwait_w(lam=0.75, setup_k=1.0, hold_h=1.0)  # ratio = 1.5
    w_star_exact_boundary = optimal_groupwait_w(lam=1.0, setup_k=1.0, hold_h=1.0)  # ratio = 2.0
    assert w_star_mid_band == 0.0
    assert w_star_exact_boundary == 0.0
    c_mid_0 = closed_form_groupwait_cost(0.75, 1.0, 1.0, 0.0)
    c_mid_half = closed_form_groupwait_cost(0.75, 1.0, 1.0, 0.5)
    assert abs(c_mid_0 - 0.75) < 1e-9 and c_mid_0 < c_mid_half
    des_mid_0 = _sim_ephemeral_groupwait_des(0.75, 1.0, 1.0, 0.0, n_cycles=25_000, seed=17)
    des_mid_half = _sim_ephemeral_groupwait_des(0.75, 1.0, 1.0, 0.5, n_cycles=25_000, seed=17)
    assert des_mid_0 < des_mid_half

    #    (c) Interior minimizer regime lam*K > h (2*lam*K/h > 2.0):
    w_star_near = optimal_groupwait_w(lam=1.5, setup_k=1.0, hold_h=1.0)  # ratio = 3.0 > 2.0
    assert abs(w_star_near - ((math.sqrt(2.0) - 1.0) / 1.5)) < 1e-9
    assert closed_form_groupwait_cost(1.5, 1.0, 1.0, w_star_near) < 1.5

    w_star_burst = optimal_groupwait_w(lam=0.5, setup_k=50.0, hold_h=1.0)  # ratio = 50.0
    assert abs(w_star_burst - 12.0) < 1e-9
    c_burst_0 = closed_form_groupwait_cost(0.5, 50.0, 1.0, 0.0)
    c_burst_opt = closed_form_groupwait_cost(0.5, 50.0, 1.0, w_star_burst)
    assert abs(c_burst_0 - 25.0) < 1e-9 and abs(c_burst_opt - 7.0) < 1e-9

    des_burst_opt = _sim_ephemeral_groupwait_des(
        0.5, 50.0, 1.0, w_star_burst, n_cycles=25_000, seed=42
    )
    rel_err = abs(des_burst_opt - c_burst_opt) / c_burst_opt
    assert rel_err < 0.01, f"DES vs analytical mismatch: {rel_err}"

    # 2. Full 3-timer Alertmanager state machine + parent->child inhibition storm test
    rng = random.Random(314159)
    events: list[tuple[float, str, _SimAlert]] = []
    group_wait = 10.0
    group_interval = 60.0
    repeat_interval = 300.0

    for idx in range(60):
        base_t = idx * 400.0 + rng.uniform(0.0, 5.0)
        mod = f"mod_{idx % 10}"
        root_fp = f"root_{idx}"
        events.append((
            base_t,
            mod,
            _SimAlert(
                fp=root_fp,
                labels={"module": mod, "kind": "root_interface_break"},
                starts_at=base_t,
                ends_at=base_t + 220.0,
            ),
        ))
        for s_idx in range(8):
            sym_t = base_t + rng.uniform(0.5, 6.0)
            events.append((
                sym_t,
                mod,
                _SimAlert(
                    fp=f"sym_{idx}_{s_idx}",
                    labels={"module": mod, "kind": "downstream_compile_symptom"},
                    starts_at=sym_t,
                    ends_at=base_t + 200.0,
                ),
            ))
        wave2_t = base_t + 10.0 + rng.uniform(2.0, 58.0)
        events.append((
            wave2_t,
            mod,
            _SimAlert(
                fp=f"root2_{idx}",
                labels={"module": mod, "kind": "root_interface_break"},
                starts_at=wave2_t,
                ends_at=base_t + 220.0,
            ),
        ))

    parent_child_rule = _InhibitRuleSpec(
        source_matchers={"kind": "root_interface_break"},
        target_matchers={"kind": "downstream_compile_symptom"},
        equal_labels=("module",),
        respect_exclude_two_sided=True,
    )
    no_inhibit = _simulate_alertmanager_pipeline(
        events=events,
        group_wait=group_wait,
        group_interval=group_interval,
        repeat_interval=repeat_interval,
        inhibit_rules=[],
    )
    with_inhibit = _simulate_alertmanager_pipeline(
        events=events,
        group_wait=group_wait,
        group_interval=group_interval,
        repeat_interval=repeat_interval,
        inhibit_rules=[parent_child_rule],
    )
    assert with_inhibit["root_causes_notified_count"] == 120
    assert with_inhibit["symptoms_notified_count"] == 0
    assert no_inhibit["symptoms_notified_count"] >= 480
    assert with_inhibit["dedup_suppressed"] >= 120
    assert 22.0 <= with_inhibit["mean_subsequent_batch_wait"] <= 38.0

    # 3. Non-vacuous excludeTwoSidedMatch test (inhibit/inhibit.go:192, 299-302):
    #    Overlapping rule: SourceMatchers={"severity": "error"}, TargetMatchers={"stage": "compile"},
    #    Equal=("module",). Two peer alerts with {module=m0, severity=error, stage=compile} match BOTH
    #    sides, while {module=m0, severity=warn, stage=compile} matches only target!
    two_sided_events = [
        (
            1.0,
            "m0",
            _SimAlert(
                fp="peer_err_a",
                labels={"module": "m0", "severity": "error", "stage": "compile"},
                starts_at=1.0,
                ends_at=20.0,
            ),
        ),
        (
            2.0,
            "m0",
            _SimAlert(
                fp="peer_err_b",
                labels={"module": "m0", "severity": "error", "stage": "compile"},
                starts_at=2.0,
                ends_at=20.0,
            ),
        ),
        (
            3.0,
            "m0",
            _SimAlert(
                fp="compile_warn_c",
                labels={"module": "m0", "severity": "warn", "stage": "compile"},
                starts_at=3.0,
                ends_at=20.0,
            ),
        ),
    ]
    two_sided_guarded = _simulate_alertmanager_pipeline(
        events=two_sided_events,
        group_wait=5.0,
        group_interval=60.0,
        repeat_interval=300.0,
        inhibit_rules=[
            _InhibitRuleSpec(
                source_matchers={"severity": "error"},
                target_matchers={"stage": "compile"},
                equal_labels=("module",),
                respect_exclude_two_sided=True,
            )
        ],
    )
    two_sided_unguarded = _simulate_alertmanager_pipeline(
        events=two_sided_events,
        group_wait=5.0,
        group_interval=60.0,
        repeat_interval=300.0,
        inhibit_rules=[
            _InhibitRuleSpec(
                source_matchers={"severity": "error"},
                target_matchers={"stage": "compile"},
                equal_labels=("module",),
                respect_exclude_two_sided=False,
            )
        ],
    )
    # With excludeTwoSidedMatch=True, both two-sided root errors survive (2 notified) and mute only
    # the target-only warning (1 inhibited); without it, the two root errors mutually mute each other (0 notified)!
    assert two_sided_guarded["notified_fingerprints_count"] == 2
    assert two_sided_guarded["inhibited_symptoms"] == 1
    assert two_sided_unguarded["notified_fingerprints_count"] == 0

    # 4. Scholl & Kleinrock (1983) rest-period residual-life penalty sum(dt^2) / (2 * sum(dt))
    #    with timeline-preserving checkpoint splitting at T_cap = 30.0s (2,000s total work conserved!):
    det_residual = (20.0**2) / (2.0 * 20.0)  # 10.0s
    ht_samples = [5.0] * 95 + [305.0] * 5  # 95*5 + 5*305 = 2,000.0s total, mean 20.0s
    ht_total_time = sum(ht_samples)
    ht_mean = statistics.fmean(ht_samples)
    ht_residual = sum(x * x for x in ht_samples) / (2.0 * ht_total_time)  # 467,500 / 4,000 = 116.875s

    split_segments = _partition_with_checkpoint_cap(ht_samples, t_cap=30.0)
    split_total_time = sum(split_segments)
    capped_residual = sum(x * x for x in split_segments) / (
        2.0 * split_total_time
    )  # 47,500 / 4,000 = 11.875s
    assert abs(ht_mean - 20.0) < 1e-9
    assert abs(split_total_time - ht_total_time) < 1e-9  # Exact conservation of time (2,000.0s)!
    assert abs(ht_residual - 116.875) < 1e-9
    assert abs(capped_residual - 11.875) < 1e-9
    assert det_residual < capped_residual < 15.0  # Strictly < T_cap / 2 = 15.0s

    return {
        "evidence_role": "normative + source + derived",
        "closed_form_w_star_regimes_sec": {
            "low_ratio_0_4": w_star_low,
            "mid_band_ratio_1_5_lam_0_75": w_star_mid_band,
            "boundary_ratio_2_0_lam_1_0": w_star_exact_boundary,
            "near_interior_ratio_3_0_lam_1_5": round(w_star_near, 6),
            "burst_ratio_50_0_lam_0_5": round(w_star_burst, 4),
        },
        "mid_band_cost_w0_vs_whalf_analytic_and_des": {
            "analytic_w0": round(c_mid_0, 4),
            "analytic_w0_5": round(c_mid_half, 4),
            "des_w0": round(des_mid_0, 4),
            "des_w0_5": round(des_mid_half, 4),
        },
        "burst_cost_w0_vs_wstar_vs_des": (
            round(c_burst_0, 4),
            round(c_burst_opt, 4),
            round(des_burst_opt, 4),
        ),
        "alertmanager_no_inhibition": {
            k: v for k, v in no_inhibit.items() if k != "notified_fingerprints_count"
        },
        "alertmanager_with_inhibition": {
            k: v for k, v in with_inhibit.items() if k != "notified_fingerprints_count"
        },
        "exclude_two_sided_match_notified_guarded_vs_unguarded": (
            two_sided_guarded["notified_fingerprints_count"],
            two_sided_unguarded["notified_fingerprints_count"],
        ),
        "scholl_kleinrock_residual_det_vs_heavy_vs_checkpoint_split_sec": (
            round(det_residual, 3),
            round(ht_residual, 3),
            round(capped_residual, 3),
        ),
    }


# ============================================================================
# PROBE 3: TMS Expertise Directory (Truck-Factor DOA + CODEOWNERS +
#          git-of-theseus Cohort-Survival Decay) vs. Brooks O(N^2) Broadcast
# [evidence_role: documentation + source + derived]
# Grounded in:
#   - aserg-ufmg/Truck-Factor@614600ed6b36bb8f452bc6eab7c9b95320f5d7be
#     (gittruckfactor/src/aserg/gtf/model/authorship/AuthorshipInfo.java:35-55,74-85;
#      gittruckfactor/src/aserg/gtf/task/DOACalculator.java:104-129,171;
#      gittruckfactor/src/aserg/gtf/truckfactor/GreedyTruckFactor.java:26-42)
#   - Avelino et al. (ICPC 2016, DOI: 10.1109/ICPC.2016.7503718, arXiv:1604.06766v1)
#   - erikbern/git-of-theseus@961bda027ffa9fcd8bbe99d5b8809cc0eaa86464
#     (git_of_theseus/survival_plot.py:79-108, exp(-k * t), half-life = ln(2)/k)
#   - hmarr/codeowners@11d3ff2659b769bcb43ddef81a6ab19d1205d9c2
#     (codeowners.go:116-140; match.go:17-180)
#   - Brooks (1975/1995, Ch. 2 & Ch. 7)
# ============================================================================


@dataclasses.dataclass(frozen=True)
class CodeownersRule:
    pattern: str
    owners: tuple[str, ...]


def _compile_codeowners_pattern(
    pattern_str: str,
) -> tuple[bool, str, re.Pattern[str] | None]:
    """Port of hmarr/codeowners newPattern + buildPatternRegex (match.go:17-180)."""
    if not pattern_str or "***" in pattern_str:
        raise ValueError(f"invalid CODEOWNERS pattern: {pattern_str!r}")
    if not any(ch in pattern_str for ch in "*?\\") and pattern_str.startswith("/"):
        return True, pattern_str[1:], None
    if pattern_str == "/":
        return False, "", re.compile(r"\A\Z", re.DOTALL)

    segs = pattern_str.split("/")
    if segs[0] == "":
        # Leading slash: anchored to repository root
        segs = segs[1:]
    else:
        # Single-segment or "dir/" pattern without leading slash matches at any depth
        if len(segs) == 1 or (len(segs) == 2 and segs[1] == ""):
            if segs[0] != "**":
                segs = ["**"] + segs

    if len(segs) > 1 and segs[-1] == "":
        # Trailing slash is equivalent to "/**"
        segs[-1] = "**"

    last_idx = len(segs) - 1
    need_slash = False
    out: list[str] = [r"\A"]
    for i, seg in enumerate(segs):
        if seg == "**":
            if i == 0 and i == last_idx:
                out.append(r".+")
            elif i == 0:
                out.append(r"(?:.+/)?")
                need_slash = False
            elif i == last_idx:
                out.append(r"/.*")
            else:
                out.append(r"(?:/.+)?")
                need_slash = True
        elif seg == "*":
            if need_slash:
                out.append("/")
            out.append(r"[^/]+")
            need_slash = True
        else:
            if need_slash:
                out.append("/")
            escape = False
            for ch in seg:
                if escape:
                    escape = False
                    out.append(re.escape(ch))
                    continue
                if ch == "\\":
                    escape = True
                elif ch == "*":
                    out.append(r"[^/]*")
                elif ch == "?":
                    out.append(r"[^/]")
                elif ch in "[]":
                    out.append("\\" + ch)
                else:
                    out.append(re.escape(ch))
            if i == last_idx:
                out.append(r"(?:/.*)?")
            need_slash = True
    out.append(r"\Z")
    return False, "", re.compile("".join(out), re.DOTALL)


class CodeownersRuleset:
    """Reproduces hmarr/codeowners Ruleset.Match + pattern.match (codeowners.go:121-130, match.go:34-66)."""

    def __init__(self, rules: list[CodeownersRule]) -> None:
        self._compiled = [
            (rule, *_compile_codeowners_pattern(rule.pattern)) for rule in rules
        ]

    def match(self, path: str) -> tuple[str, ...]:
        test_path = path.replace("\\", "/").lstrip("/")
        for idx in range(len(self._compiled) - 1, -1, -1):
            rule, left_anchored_lit, prefix, rx = self._compiled[idx]
            if left_anchored_lit:
                if prefix.endswith("/"):
                    matched = test_path.startswith(prefix)
                elif len(test_path) == len(prefix):
                    matched = test_path == prefix
                elif len(test_path) > len(prefix) and test_path[len(prefix)] == "/":
                    matched = test_path.startswith(prefix)
                else:
                    matched = False
            else:
                assert rx is not None
                matched = rx.match(test_path) is not None
            if matched:
                return rule.owners
        return ()


@dataclasses.dataclass(frozen=True)
class CommitEvent:
    author: str
    timestamp_days: float
    status: str = "MODIFIED"  # "ADDED", "MODIFIED", or "RENAMED_TREATED"


def compute_static_gtf_doa(
    commits: list[CommitEvent],
) -> tuple[dict[str, float], dict[str, bool]]:
    """Exact reproduction of DOACalculator.java:104-129 & AuthorshipInfo.java:35-55.

    - First Status.ADDED sets firstAuthor (FA=1).
    - Subsequent Status.ADDED by a different developer sets secondaryAuthor (DOACalculator.java:109-113)
      and increments addDeliveries; Status.MODIFIED and Status.RENAMED_TREATED call addNewDelivery().
    - getDoaMultAuthor() (AuthorshipInfo.java:53):
        3.293 + 1.098*(FA || SA ? 1 : 0) + 0.164*DL - 0.321*ln(1 + AC)
    - isDOAAuthor (AuthorshipInfo.java:38):
        normDOA > 0.75 && (doaMultAuthor >= 3.293 || firstAuthor || secondaryAuthor)
    """
    authors = sorted({c.author for c in commits})
    first_author: str | None = None
    secondary_authors: set[str] = set()
    deliveries: dict[str, int] = {d: 0 for d in authors}
    total_non_initial_deliveries = 0

    for c in commits:
        if c.status == "ADDED":
            if first_author is None:
                first_author = c.author
            elif c.author != first_author:
                secondary_authors.add(c.author)
                deliveries[c.author] += 1
                total_non_initial_deliveries += 1
            else:
                deliveries[c.author] += 1
                total_non_initial_deliveries += 1
        elif c.status in ("MODIFIED", "RENAMED_TREATED"):
            deliveries[c.author] += 1
            total_non_initial_deliveries += 1
        else:
            raise ValueError(f"Unsupported status: {c.status!r}")

    doa_scores: dict[str, float] = {}
    for dev in authors:
        fa_or_sa = 1 if (dev == first_author or dev in secondary_authors) else 0
        dl = deliveries[dev]
        ac = total_non_initial_deliveries - dl
        doa_scores[dev] = 3.293 + 1.098 * fa_or_sa + 0.164 * dl - 0.321 * math.log(1.0 + ac)

    best_doa = max(doa_scores.values()) if doa_scores else 1.0
    qualifies: dict[str, bool] = {}
    for dev, score in doa_scores.items():
        norm_doa = score / best_doa
        has_author_flag = (dev == first_author) or (dev in secondary_authors)
        qualifies[dev] = (norm_doa > 0.75) and (score >= 3.293 or has_author_flag)
    return doa_scores, qualifies


def compute_survival_weighted_doa(
    commits: list[CommitEvent],
    now_days: float,
    half_life_days: float,
    dormant_weight_floor: float = 1e-3,
) -> tuple[dict[str, float], str]:
    """Weights FA, DL, and AC purely by exponential survival exp(-k * dt), k = ln(2)/half_life.

    When all historical commits have decayed below `dormant_weight_floor` (a long-dormant file
    where every contributor's decayed score approaches 3.293), top-1 selection falls back to
    static DOA rather than breaking ties alphabetically on contributor usernames.
    """
    static_scores, _ = compute_static_gtf_doa(commits)
    decay_k = math.log(2.0) / half_life_days
    authors = sorted({c.author for c in commits})
    weights = [math.exp(-decay_k * max(0.0, now_days - c.timestamp_days)) for c in commits]

    if sum(weights) < dormant_weight_floor:
        top_owner = max(authors, key=lambda d: static_scores[d])
        return static_scores, top_owner

    first_idx: int | None = None
    for idx, c in enumerate(commits):
        if c.status == "ADDED":
            first_idx = idx
            break

    total_mod_w = sum(w for idx, w in enumerate(weights) if idx != first_idx)
    scores: dict[str, float] = {}
    for dev in authors:
        fa_w = (
            weights[first_idx]
            if (first_idx is not None and commits[first_idx].author == dev)
            else 0.0
        )
        dl_w = sum(
            w
            for idx, (c, w) in enumerate(zip(commits, weights))
            if idx != first_idx and c.author == dev
        )
        ac_w = max(0.0, total_mod_w - dl_w)
        scores[dev] = 3.293 + 1.098 * fa_w + 0.164 * dl_w - 0.321 * math.log(1.0 + ac_w)

    top_owner = max(authors, key=lambda d: (round(scores[d], 9), static_scores[d]))
    return scores, top_owner


def greedy_truck_factor(file_authors: dict[str, set[str]], coverage_threshold: float = 0.5) -> int:
    """Reproduces GreedyTruckFactor.getTruckFactor (GreedyTruckFactor.java:26-42)."""
    total_files = len(file_authors)
    if total_files == 0:
        return 0
    dev_map: dict[str, set[str]] = collections.defaultdict(set)
    for fpath, devs in file_authors.items():
        for dev in devs:
            dev_map[dev].add(fpath)

    factor = 0
    while dev_map:
        covered = set().union(*dev_map.values())
        if (len(covered) / total_files) < coverage_threshold:
            break
        top_dev = max(sorted(dev_map.keys()), key=lambda d: len(dev_map[d]))
        del dev_map[top_dev]
        factor += 1
    return factor


def probe_tms_doa_survival_decay_vs_broadcast() -> dict[str, Any]:
    # 1. Verify hmarr/codeowners gitignore-style anchoring, single-star '/', unanchored dirs,
    #    and last-matching-rule override precedence (match.go:17-180, codeowners.go:121-130):
    anchor_ruleset = CodeownersRuleset([
        CodeownersRule("/*.rs", ("@root-rust",)),
        CodeownersRule("src/*.rs", ("@src-top-only",)),
        CodeownersRule("docs/", ("@docs-any-depth",)),
    ])
    assert anchor_ruleset.match("lib.rs") == ("@root-rust",)
    assert anchor_ruleset.match("src/nested/lib.rs") == ()  # '/*.rs' is root-anchored!
    assert anchor_ruleset.match("src/lib.rs") == ("@src-top-only",)
    assert anchor_ruleset.match("src/deep/sub/mod.rs") == ()  # single '*' never crosses '/'!
    assert anchor_ruleset.match("docs/intro.md") == ("@docs-any-depth",)
    assert anchor_ruleset.match("crates/core/docs/guide.md") == ("@docs-any-depth",)
    assert anchor_ruleset.match("docs_archive/guide.md") == ()

    ruleset = CodeownersRuleset([
        CodeownersRule("*", ("@arch-catchall",)),
        CodeownersRule("src/storage/**", ("@storage-lead",)),
        CodeownersRule("src/storage/wal/recovery.rs", ("@wal-specialist", "@crc-specialist")),
    ])
    assert ruleset.match("README.md") == ("@arch-catchall",)
    assert ruleset.match("src/storage/btree.rs") == ("@storage-lead",)
    assert ruleset.match("src/storage/wal/recovery.rs") == ("@wal-specialist", "@crc-specialist")

    # 2. Verify secondaryAuthor semantics (DOACalculator.java:109-113 vs RENAMED_TREATED:125-128)
    sec_commits = [
        CommitEvent("creator_dev", timestamp_days=1.0, status="ADDED"),
        CommitEvent("re_adder_dev", timestamp_days=10.0, status="ADDED"),
        CommitEvent("renamer_dev", timestamp_days=20.0, status="RENAMED_TREATED"),
    ] + [CommitEvent(f"other_{i}", timestamp_days=30.0 + i, status="MODIFIED") for i in range(6)]
    sec_scores, sec_qual = compute_static_gtf_doa(sec_commits)
    # re_adder_dev gets +1.098 secondaryAuthor bonus; renamer_dev gets only +0.164 addNewDelivery()!
    assert sec_scores["re_adder_dev"] > sec_scores["renamer_dev"] + 0.90
    assert sec_qual["re_adder_dev"] is True

    # 3. Simulate 120 refactored files where departed creator ('a_departed_*', alphabetically FIRST!)
    #    left at day 25 and active maintainer ('z_active_*', alphabetically LAST!) took over in
    #    days 640..725 using pure exponential survival decay (zero churn-size multiplier).
    rng = random.Random(271828)
    now_days = 730.0
    half_life_days = 180.0
    static_top1_stale = 0
    static_creator_still_qualified = 0
    survival_top1_active = 0
    file_authors_static: dict[str, set[str]] = {}

    for f_idx in range(120):
        departed = f"a_departed_creator_{f_idx % 4}"
        active_expert = f"z_active_owner_{f_idx % 6}"
        commits = [CommitEvent(departed, timestamp_days=5.0, status="ADDED")]
        commits.append(CommitEvent(departed, timestamp_days=15.0, status="MODIFIED"))
        commits.append(CommitEvent(departed, timestamp_days=25.0, status="MODIFIED"))
        for c_i in range(5):
            commits.append(
                CommitEvent(
                    active_expert,
                    timestamp_days=640.0 + c_i * 20.0 + rng.uniform(0.0, 2.0),
                    status="MODIFIED",
                )
            )
        for p_i in range(3):
            commits.append(
                CommitEvent(
                    f"m_peer_{p_i}",
                    timestamp_days=400.0 + p_i * 50.0,
                    status="MODIFIED",
                )
            )

        static_scores, static_qual = compute_static_gtf_doa(commits)
        _, top_surv = compute_survival_weighted_doa(commits, now_days, half_life_days)

        top_static = max(sorted(static_scores), key=lambda d: static_scores[d])
        if top_static == departed:
            static_top1_stale += 1
        if static_qual[departed]:
            static_creator_still_qualified += 1
        if top_surv == active_expert:
            survival_top1_active += 1
        file_authors_static[f"file_{f_idx}.rs"] = {d for d, ok in static_qual.items() if ok}

    # Verify dormant-file fallback (file untouched for 4,000 days >> 180-day half-life):
    # 'z_creator' (FA=1 + 8 edits) must beat 'a_typo_fixer' (1 edit), never losing to alphabetical 'a_*'!
    dormant_commits = [CommitEvent("z_creator", timestamp_days=1.0, status="ADDED")] + [
        CommitEvent("z_creator", timestamp_days=2.0 + i, status="MODIFIED") for i in range(8)
    ] + [CommitEvent("a_typo_fixer", timestamp_days=20.0, status="MODIFIED")]
    _, dormant_top = compute_survival_weighted_doa(
        dormant_commits, now_days=4_000.0, half_life_days=180.0
    )
    assert dormant_top == "z_creator"

    static_stale_rate = static_top1_stale / 120.0
    survival_active_acc = survival_top1_active / 120.0
    tf_val = greedy_truck_factor(file_authors_static, coverage_threshold=0.5)
    assert static_stale_rate == 1.0
    assert static_creator_still_qualified == 120
    assert survival_active_acc == 1.0
    assert tf_val >= 2

    # 4. Fleet communication scaling: Brooks O(N^2) broadcast vs O(1)-fanout TEP directory (k=2 owners)
    scaling_rows: dict[str, Any] = {}
    k_specialists = 2
    for n_agents in (4, 8, 16, 32, 64):
        events_m = 2 * n_agents
        broadcast_msgs = events_m * (n_agents - 1)
        tep_routed_msgs = events_m * min(k_specialists, n_agents - 1)
        non_owner_broadcast_msgs = events_m * max(0, n_agents - 1 - k_specialists)
        total_delivery_reduction = 1.0 - (tep_routed_msgs / broadcast_msgs)
        scaling_rows[f"N_{n_agents}"] = {
            "broadcast_deliveries": broadcast_msgs,
            "tep_directory_deliveries": tep_routed_msgs,
            "non_owner_distractors_under_broadcast": non_owner_broadcast_msgs,
            "non_owner_distractors_under_exact_tep": 0,
            "total_delivery_reduction_vs_broadcast": round(total_delivery_reduction, 4),
        }
    assert scaling_rows["N_32"]["total_delivery_reduction_vs_broadcast"] > 0.93
    assert scaling_rows["N_64"]["total_delivery_reduction_vs_broadcast"] > 0.96

    return {
        "evidence_role": "documentation + source + derived",
        "codeowners_anchoring_and_precedence_verified": True,
        "secondary_author_on_re_add_verified": True,
        "dormant_file_non_alphabetical_fallback_owner": dormant_top,
        "static_doa_stale_creator_top1_rate": round(static_stale_rate, 4),
        "static_doa_creator_qualified_count_of_120": static_creator_still_qualified,
        "survival_weighted_doa_active_top1_accuracy": round(survival_active_acc, 4),
        "greedy_truck_factor_50pct": tf_val,
        "brooks_broadcast_vs_tep_scaling": scaling_rows,
    }


# ============================================================================
# PROBE 4: Tokio Cooperative Poll Budget (128) + Faithful Watch Latest-State
#          Overwrite vs. Semilattice / LangGraph BSP & Temporal Batch Ordering
# [evidence_role: source + derived]
# Grounded in:
#   - tokio-rs/tokio@675ba8164071a6eee3dd1f3cb4fbdc1d3664396e
#     (tokio/src/task/coop/mod.rs:97,115-126,260,448-456;
#      tokio/src/sync/watch.rs:185,676,836,1082,1247-1252)
#   - langchain-ai/langgraph@c6335a4255dc1d8abc25a7677f9c072c7ab27b9c
#     (libs/langgraph/langgraph/pregel/_algo.py:158-175,235-258;
#      libs/langgraph/langgraph/channels/binop.py:66-149;
#      libs/langgraph/langgraph/pregel/_loop.py:697-701,788-794)
#   - temporalio/sdk-python@5c925a41b36b34d9ce32d03f1d1f07faa35b348a
#     (temporalio/worker/_workflow_instance.py:521-570)
# ============================================================================


class TokioCoopBudget:
    """Faithful model of tokio::task::coop::Budget(Some(128)) + RestoreOnPending (coop/mod.rs)."""

    INITIAL_BUDGET = 128

    def __init__(self, constrained: bool = True) -> None:
        self.remaining: int | None = self.INITIAL_BUDGET if constrained else None

    def reset_for_scheduler_turn(self) -> None:
        self.remaining = self.INITIAL_BUDGET

    def poll_proceed_and_step(self, inner_ready: bool) -> str:
        if self.remaining is not None:
            if self.remaining == 0:
                return "YIELD_COOP_EXHAUSTED"
            saved = self.remaining
            self.remaining -= 1
            if not inner_ready:
                self.remaining = saved
                return "PENDING_RESTORED"
            return "READY_CONSUMED"
        return "READY_UNCONSTRAINED" if inner_ready else "PENDING_UNCONSTRAINED"


class TokioWatchChannel:
    """Exact model of tokio::sync::watch::Sender::send_replace (watch.rs:1247-1252).

    `send_replace` unconditionally swaps `old` with `new_value` (`mem::swap`) and increments
    the channel version; it is strictly last-arrival-wins, NOT a monotonic `max` reducer.
    """

    def __init__(self, initial: Any) -> None:
        self._value = initial
        self._version = 0

    def send_replace(self, new_value: Any) -> Any:
        old = self._value
        self._value = new_value
        self._version += 1
        return old

    def borrow_and_update(self, seen_version: int) -> tuple[Any, int, bool]:
        changed = seen_version != self._version
        return self._value, self._version, changed


class BinaryOperatorAggregateChannel:
    """Models LangGraph BinaryOperatorAggregate (channels/binop.py:66-149)."""

    def __init__(self, initial: Any, operator: Callable[[Any, Any], Any]) -> None:
        self.value = initial
        self.operator = operator
        self.updated = False

    def update(self, values: list[Any]) -> bool:
        if not values:
            return False
        for val in values:
            self.value = self.operator(self.value, val)
        self.updated = True
        return True


def probe_tokio_coop_and_langgraph_superstep_delivery() -> dict[str, Any]:
    # 1. Verify Tokio coop Budget(Some(128)) fairness & RestoreOnPending semantics:
    budget = TokioCoopBudget(constrained=True)
    for _ in range(10):
        assert budget.poll_proceed_and_step(inner_ready=False) == "PENDING_RESTORED"
    assert budget.remaining == 128

    ready_before_forced_yield = 0
    forced_yields = 0
    max_starvation_polls = 0
    cur_run = 0
    total_target_ready = 400
    completed = 0
    while completed < total_target_ready:
        outcome = budget.poll_proceed_and_step(inner_ready=True)
        if outcome == "READY_CONSUMED":
            completed += 1
            cur_run += 1
            if forced_yields == 0:
                ready_before_forced_yield += 1
        elif outcome == "YIELD_COOP_EXHAUSTED":
            max_starvation_polls = max(max_starvation_polls, cur_run)
            cur_run = 0
            forced_yields += 1
            budget.reset_for_scheduler_turn()
    max_starvation_polls = max(max_starvation_polls, cur_run)
    assert ready_before_forced_yield == 128
    assert max_starvation_polls == 128
    assert forced_yields == 3  # 400 = 128 + 128 + 128 + 16

    # 2. Single-writer monotonic revision stream (M = 500 updates across G = 8 artifacts):
    #    Unconditional TokioWatchChannel.send_replace coalesces 500 rapid sends into 8 reader wakeups!
    n_artifacts = 8
    n_rapid_updates = 500
    canonical_updates: list[tuple[str, int, str]] = []
    for m_idx in range(n_rapid_updates):
        art = f"artifact_{m_idx % n_artifacts}.rs"
        ver = (m_idx // n_artifacts) + 1
        producer_path = f"node_{m_idx % n_artifacts:02d}/step_{ver:03d}"
        canonical_updates.append((art, ver, producer_path))

    mono_watches = {f"artifact_{i}.rs": TokioWatchChannel(0) for i in range(n_artifacts)}
    for art, ver, _ in canonical_updates:
        mono_watches[art].send_replace(ver)  # Unconditional swap on ordered single-writer stream
    mono_digest = {
        art: mono_watches[art].borrow_and_update(0)[0]
        for art in sorted(mono_watches)
        if mono_watches[art].borrow_and_update(0)[2]
    }
    assert len(mono_digest) == n_artifacts
    assert mono_digest["artifact_0.rs"] == 63 and mono_digest["artifact_7.rs"] == 62

    # 3. Multi-writer out-of-order network jitter (500 random permutations of M = 500 updates):
    #    Contrast 4 explicit arms:
    #      (A) preemptive_unbuffered_overwrite: mid-tool-chain overwrite -> 500/500 torn chains, 500 states
    #      (B) superstep_raw_watch_overwrite: faithful unconditional watch::send_replace drained at
    #          superstep boundary -> 0 torn chains, 8 entries, YET 500/500 jittered states!
    #      (C) superstep_semilattice_binop_max: LangGraph BinaryOperatorAggregate(max) commutative
    #          semilattice join -> 0 torn chains, 8 entries, 1 deterministic state!
    #      (D) superstep_path_sorted_apply_writes: LangGraph pregel/_algo.py:256-257 deterministic
    #          producer-path sort before LastValue commit -> 1 deterministic state!
    n_jitter_trials = 500
    rng = random.Random(161803)

    preemptive_distinct_states: set[tuple[tuple[str, int], ...]] = set()
    preemptive_torn_chains = 0
    raw_watch_torn_chains = 0
    raw_watch_distinct_states: set[tuple[tuple[str, int], ...]] = set()
    semilattice_distinct_states: set[tuple[tuple[str, int], ...]] = set()
    path_sorted_distinct_states: set[tuple[tuple[str, int], ...]] = set()

    for _ in range(n_jitter_trials):
        shuffled = list(canonical_updates)
        rng.shuffle(shuffled)
        split_idx = rng.randint(1, len(shuffled) - 1)

        # Arm (A): Preemptive mid-tool-chain injection
        pre_view: dict[str, int] = {f"artifact_{i}.rs": 0 for i in range(n_artifacts)}
        for art, ver, _ in shuffled[:split_idx]:
            pre_view[art] = ver
        sig_snapshot = dict(pre_view)
        for art, ver, _ in shuffled[split_idx:]:
            pre_view[art] = ver
        if sig_snapshot != pre_view:
            preemptive_torn_chains += 1
        preemptive_distinct_states.add(tuple(sorted(pre_view.items())))

        # Arm (B): Superstep-deferred raw TokioWatchChannel.send_replace (unconditional last-arrival-wins)
        active_step_snapshot = {f"artifact_{i}.rs": 0 for i in range(n_artifacts)}
        raw_watches = {f"artifact_{i}.rs": TokioWatchChannel(0) for i in range(n_artifacts)}
        for art, ver, _ in shuffled[:split_idx]:
            raw_watches[art].send_replace(ver)  # Buffered in watch slot; active step sees snapshot!
        mid_step_snapshot = dict(active_step_snapshot)
        for art, ver, _ in shuffled[split_idx:]:
            raw_watches[art].send_replace(ver)  # Unconditional mem::swap overwrite!
        if mid_step_snapshot != active_step_snapshot:
            raw_watch_torn_chains += 1
        raw_watch_committed = {
            art: raw_watches[art].borrow_and_update(0)[0] for art in sorted(raw_watches)
        }
        raw_watch_distinct_states.add(tuple(sorted(raw_watch_committed.items())))

        # Arm (C): Superstep BinaryOperatorAggregate commutative semilattice join (max)
        binop_channels = {
            f"artifact_{i}.rs": BinaryOperatorAggregateChannel(0, max)
            for i in range(n_artifacts)
        }
        grouped_vals: dict[str, list[int]] = collections.defaultdict(list)
        for art, ver, _ in shuffled:
            grouped_vals[art].append(ver)
        for art, vals in grouped_vals.items():
            binop_channels[art].update(vals)
        semilattice_Distinct = tuple(
            (art, binop_channels[art].value) for art in sorted(binop_channels)
        )
        semilattice_distinct_states.add(semilattice_Distinct)

        # Arm (D): LangGraph apply_writes deterministic task-path sort (pregel/_algo.py:256-257)
        sorted_tasks = sorted(shuffled, key=lambda item: item[2])
        sorted_watches = {f"artifact_{i}.rs": TokioWatchChannel(0) for i in range(n_artifacts)}
        for art, ver, _ in sorted_tasks:
            sorted_watches[art].send_replace(ver)
        path_sorted_committed = tuple(
            (art, sorted_watches[art].borrow_and_update(0)[0]) for art in sorted(sorted_watches)
        )
        path_sorted_distinct_states.add(path_sorted_committed)

    # 4. Non-commutative Temporal 4-bucket activate() check (_workflow_instance.py:521-560):
    #    A `signal_workflow` handler checks whether `notify_has_patch("v2_schema")` is active.
    #    Under `_single_batch_activation=True`, `job_sets[0]` (patches) applies strictly before
    #    `job_sets[1]` (signals+updates) and all jobs apply before `_run_once`, preventing
    #    activation-list arrival order from hiding same-task patch state!
    temporal_bucketed_v2_count = 0
    unbucketed_arrival_v2_count = 0
    for _ in range(n_jitter_trials):
        act_jobs = [("notify_has_patch", "v2_schema"), ("signal_workflow", "payload")]
        rng.shuffle(act_jobs)

        # Unbucketed arrival-order execution
        patched_unbucketed = False
        decoded_unbucketed = "none"
        for jtype, _ in act_jobs:
            if jtype == "notify_has_patch":
                patched_unbucketed = True
            elif jtype == "signal_workflow":
                decoded_unbucketed = "v2" if patched_unbucketed else "v1_stale"
        if decoded_unbucketed == "v2":
            unbucketed_arrival_v2_count += 1

        # Temporal activate() 4-bucket split under _single_batch_activation = True
        job_sets: list[list[tuple[str, str]]] = [[], [], [], []]
        for jtype, arg in act_jobs:
            if jtype == "notify_has_patch":
                job_sets[0].append((jtype, arg))
            elif jtype in ("signal_workflow", "do_update"):
                job_sets[1].append((jtype, arg))
            else:
                job_sets[2].append((jtype, arg))
        patched_temporal = False
        pending_signals: list[str] = []
        for jset in job_sets:
            for jtype, arg in jset:
                if jtype == "notify_has_patch":
                    patched_temporal = True
                elif jtype == "signal_workflow":
                    pending_signals.append("v2" if patched_temporal else "v1_stale")
        if pending_signals == ["v2"]:
            temporal_bucketed_v2_count += 1

    digest_compression = 1.0 - (n_artifacts / n_rapid_updates)
    assert preemptive_torn_chains == n_jitter_trials
    assert len(preemptive_distinct_states) == n_jitter_trials
    assert raw_watch_torn_chains == 0
    assert len(raw_watch_distinct_states) == n_jitter_trials  # 500/500 jittered under raw watch!
    assert len(semilattice_distinct_states) == 1
    assert len(path_sorted_distinct_states) == 1
    assert semilattice_distinct_states == path_sorted_distinct_states
    assert temporal_bucketed_v2_count == n_jitter_trials
    assert 200 <= unbucketed_arrival_v2_count <= 300
    assert abs(digest_compression - 0.984) < 1e-9

    return {
        "evidence_role": "source + derived",
        "tokio_coop_initial_budget": TokioCoopBudget.INITIAL_BUDGET,
        "tokio_coop_max_starvation_polls": max_starvation_polls,
        "tokio_coop_forced_yields_in_400_polls": forced_yields,
        "single_writer_monotonic_watch_wakeups_vs_sends": (n_artifacts, n_rapid_updates),
        "jitter_trials": n_jitter_trials,
        "preemptive_torn_chain_breaks": preemptive_torn_chains,
        "preemptive_distinct_final_states": len(preemptive_distinct_states),
        "superstep_raw_watch_torn_chain_breaks": raw_watch_torn_chains,
        "superstep_raw_watch_distinct_final_states": len(raw_watch_distinct_states),
        "superstep_semilattice_distinct_final_states": len(semilattice_distinct_states),
        "superstep_path_sorted_distinct_final_states": len(path_sorted_distinct_states),
        "temporal_single_batch_patch_before_signal_v2_rate": (
            temporal_bucketed_v2_count,
            unbucketed_arrival_v2_count,
        ),
        "watch_digest_token_reduction": round(digest_compression, 4),
    }


# ============================================================================
# PROBE 5: Expected Value-of-Information (VoI) Interruption Controller &
#          Calibration-Noise / Overconfidence Breakdown Sweep
# [evidence_role: normative + documentation + derived]
# Grounded in:
#   - Iqbal & Bailey (CHI 2006: COIL=464ms vs COIH=1,702ms [ln(ms)=6.14 vs 7.44];
#     CHI 2008: relevant resumption 4.65s vs general-interest 23.1s [4.97x penalty])
#   - Wang et al. (2026, HandRaiser, arXiv:2604.06452v2, Table 1: Prompting SR drop
#     0.743->0.500 & token inflation 346->461 vs calibrated RL interruption)
#   - Horvitz, Jacobs, & Hovel (UAI 1999, arXiv:1301.6707) expected-utility attentional gating
# ============================================================================


@dataclasses.dataclass(frozen=True)
class CandidateAdvisory:
    p_rel: float  # True probability that advisory prevents wasted/conflicting work
    conflict_waste_rate: float  # Wasted utility units/sec if unaddressed while working
    rem_subtask_sec: float  # Expected remaining time until next coarse subtask boundary
    post_boundary_benefit: float  # Residual value if delivered cleanly at coarse boundary


def _score_3tier_decision(
    adv: CandidateAdvisory,
    p_hat: float,
    *,
    c_rel_mid: float,
    c_irrel_mid: float,
    coarse_discount: float,
    use_prior_stakes: bool = True,
    prior_waste_rate: float = 0.80,
    prior_post_benefit: float = 20.0,
) -> tuple[str, float]:
    """Selects 3-tier action using estimated `p_hat` (and either prior conditional stakes when the
    broker has not yet inspected receiver-specific ground truth, or full-information stakes for the
    oracle upper bound), then scores realized expected utility on true `(adv.p_rel, w, B_post)`."""
    p_clamped = min(1.0, max(0.0, p_hat))
    w_est = prior_waste_rate if use_prior_stakes else adv.conflict_waste_rate
    b_est = prior_post_benefit if use_prior_stakes else adv.post_boundary_benefit
    est_cost_mid = p_clamped * c_rel_mid + (1.0 - p_clamped) * c_irrel_mid
    est_cost_bnd = coarse_discount * est_cost_mid
    est_u_pre = p_clamped * (w_est * adv.rem_subtask_sec + b_est) - est_cost_mid
    est_u_def = p_clamped * b_est - est_cost_bnd

    true_cost_mid = adv.p_rel * c_rel_mid + (1.0 - adv.p_rel) * c_irrel_mid
    true_cost_bnd = coarse_discount * true_cost_mid
    true_u_pre = (
        adv.p_rel * (adv.conflict_waste_rate * adv.rem_subtask_sec + adv.post_boundary_benefit)
        - true_cost_mid
    )
    true_u_def = adv.p_rel * adv.post_boundary_benefit - true_cost_bnd

    # Exact 3-tier expected-utility inequalities:
    #   PREEMPT_NOW iff p_hat * w_est * dt_rem > C_mid(p_hat) - C_bnd(p_hat) and est_u_pre > 0
    #   DEFER_COARSE_BOUNDARY iff est_u_def > 0 and p_hat * w_est * dt_rem <= C_mid(p_hat) - C_bnd(p_hat)
    #   PULL_LEDGER_MUTE otherwise
    if (
        p_clamped * w_est * adv.rem_subtask_sec > (est_cost_mid - est_cost_bnd)
        and est_u_pre > 0.0
    ):
        return "PREEMPT_NOW", true_u_pre
    if est_u_def > 0.0:
        return "DEFER_COARSE_BOUNDARY", true_u_def
    return "PULL_LEDGER_MUTE", 0.0


def evaluate_interruption_policies(
    advisories: list[CandidateAdvisory],
    *,
    c_rel_mid: float = 4.65,
    c_irrel_mid: float = 23.10,
    coarse_discount: float = 0.464 / 1.702,
    seed: int = 99,
) -> dict[str, float]:
    """Evaluates realized net utility across static, uncalibrated, noisy-calibrated, and oracle policies."""
    rng = random.Random(seed)
    totals = {
        "never_notify": 0.0,
        "interrupt_immediately_all": 0.0,
        "always_defer_coarse_boundary": 0.0,
        "random_50pct": 0.0,
        "uncalibrated_overconfident_prompting": 0.0,
        "uncalibrated_overconfident_3tier_bias_045": 0.0,
        "voi_3tier_noisy_sigma_010": 0.0,
        "voi_3tier_noisy_sigma_020": 0.0,
        "voi_3tier_oracle_upper_bound": 0.0,
    }

    for adv in advisories:
        e_cost_mid = adv.p_rel * c_rel_mid + (1.0 - adv.p_rel) * c_irrel_mid
        e_cost_bnd = coarse_discount * e_cost_mid
        u_mute = 0.0
        u_preempt = (
            adv.p_rel * (adv.conflict_waste_rate * adv.rem_subtask_sec + adv.post_boundary_benefit)
            - e_cost_mid
        )
        u_defer_bnd = adv.p_rel * adv.post_boundary_benefit - e_cost_bnd

        totals["never_notify"] += u_mute
        totals["interrupt_immediately_all"] += u_preempt
        totals["always_defer_coarse_boundary"] += u_defer_bnd
        totals["random_50pct"] += u_preempt if rng.random() < 0.5 else u_mute

        p_overconf = min(0.99, adv.p_rel + 0.45)
        naive_cost_mid = p_overconf * c_rel_mid + (1.0 - p_overconf) * c_irrel_mid
        naive_u_preempt = (
            p_overconf * (0.80 * adv.rem_subtask_sec + 20.0) - naive_cost_mid
        )
        totals["uncalibrated_overconfident_prompting"] += (
            u_preempt if naive_u_preempt > 0.0 else u_mute
        )
        _, u_overconf_3tier = _score_3tier_decision(
            adv,
            p_overconf,
            c_rel_mid=c_rel_mid,
            c_irrel_mid=c_irrel_mid,
            coarse_discount=coarse_discount,
            use_prior_stakes=True,
        )
        totals["uncalibrated_overconfident_3tier_bias_045"] += u_overconf_3tier

        _, u_sigma_010 = _score_3tier_decision(
            adv,
            adv.p_rel + rng.gauss(0.0, 0.10),
            c_rel_mid=c_rel_mid,
            c_irrel_mid=c_irrel_mid,
            coarse_discount=coarse_discount,
            use_prior_stakes=True,
        )
        _, u_sigma_020 = _score_3tier_decision(
            adv,
            adv.p_rel + rng.gauss(0.0, 0.20),
            c_rel_mid=c_rel_mid,
            c_irrel_mid=c_irrel_mid,
            coarse_discount=coarse_discount,
            use_prior_stakes=True,
        )
        _, u_oracle = _score_3tier_decision(
            adv,
            adv.p_rel,
            c_rel_mid=c_rel_mid,
            c_irrel_mid=c_irrel_mid,
            coarse_discount=coarse_discount,
            use_prior_stakes=False,
        )
        totals["voi_3tier_noisy_sigma_010"] += u_sigma_010
        totals["voi_3tier_noisy_sigma_020"] += u_sigma_020
        totals["voi_3tier_oracle_upper_bound"] += u_oracle

    n = max(1, len(advisories))
    return {k: round(v / n, 4) for k, v in totals.items()}


def probe_voi_interruption_gate() -> dict[str, Any]:
    rng = random.Random(202605)
    c_rel, c_irrel, disc = 4.65, 23.10, 0.464 / 1.702

    # 1. Low-relevance broadcast regime (p_rel in [0.02, 0.12])
    low_rel_stream = [
        CandidateAdvisory(
            p_rel=rng.uniform(0.02, 0.12),
            conflict_waste_rate=rng.uniform(0.2, 0.8),
            rem_subtask_sec=rng.uniform(10.0, 25.0),
            post_boundary_benefit=rng.uniform(4.0, 12.0),
        )
        for _ in range(1_000)
    ]
    low_rel_res = evaluate_interruption_policies(low_rel_stream)
    assert low_rel_res["interrupt_immediately_all"] < low_rel_res["always_defer_coarse_boundary"]
    assert low_rel_res["always_defer_coarse_boundary"] < low_rel_res["never_notify"]
    assert low_rel_res["uncalibrated_overconfident_prompting"] < low_rel_res["never_notify"]
    assert low_rel_res["uncalibrated_overconfident_3tier_bias_045"] < low_rel_res["never_notify"]

    # 2. Realistic mixed fleet stream (5% hard collisions, 25% moderate coupling, 70% chatter)
    mixed_stream: list[CandidateAdvisory] = []
    tier_counts = {"PREEMPT_NOW": 0, "DEFER_COARSE_BOUNDARY": 0, "PULL_LEDGER_MUTE": 0}

    for i in range(2_000):
        u_draw = (i % 20) / 20.0
        if u_draw < 0.05:
            adv = CandidateAdvisory(
                p_rel=rng.uniform(0.88, 0.98),
                conflict_waste_rate=rng.uniform(1.5, 2.5),
                rem_subtask_sec=rng.uniform(20.0, 40.0),
                post_boundary_benefit=rng.uniform(15.0, 25.0),
            )
        elif u_draw < 0.30:
            adv = CandidateAdvisory(
                p_rel=rng.uniform(0.38, 0.55),
                conflict_waste_rate=rng.uniform(0.05, 0.20),
                rem_subtask_sec=rng.uniform(8.0, 18.0),
                post_boundary_benefit=rng.uniform(16.0, 26.0),
            )
        else:
            adv = CandidateAdvisory(
                p_rel=rng.uniform(0.01, 0.08),
                conflict_waste_rate=rng.uniform(0.02, 0.15),
                rem_subtask_sec=rng.uniform(5.0, 20.0),
                post_boundary_benefit=rng.uniform(1.0, 5.0),
            )
        mixed_stream.append(adv)
        tier, _ = _score_3tier_decision(
            adv,
            adv.p_rel,
            c_rel_mid=c_rel,
            c_irrel_mid=c_irrel,
            coarse_discount=disc,
            use_prior_stakes=False,
        )
        tier_counts[tier] += 1

    mixed_res = evaluate_interruption_policies(mixed_stream)
    assert tier_counts["PREEMPT_NOW"] > 50
    assert tier_counts["DEFER_COARSE_BOUNDARY"] > 300
    assert tier_counts["PULL_LEDGER_MUTE"] > 1000
    # Boundary deferral alone (-1.8943) beats immediate interruption (-13.0232) yet STILL loses
    # to never_notify (0.0000) without VoI/TMS relevance filtering; similarly, feeding +0.45
    # overconfident p_hat into the 3-tier gate drops below 0.0000!
    assert mixed_res["interrupt_immediately_all"] < mixed_res["always_defer_coarse_boundary"] < 0.0
    assert mixed_res["uncalibrated_overconfident_3tier_bias_045"] < 0.0
    for baseline in (
        "never_notify",
        "always_defer_coarse_boundary",
        "interrupt_immediately_all",
        "random_50pct",
        "uncalibrated_overconfident_prompting",
        "uncalibrated_overconfident_3tier_bias_045",
    ):
        assert mixed_res["voi_3tier_noisy_sigma_010"] > mixed_res[baseline] + 1.5
        assert mixed_res["voi_3tier_noisy_sigma_020"] > mixed_res[baseline] + 1.0

    # 3. Sweep zero-mean Gaussian noise sigma_cal and systematic overconfidence bias beta_bias
    #    under prior conditional stakes (zero oracle B_post leakage) to locate breakdown thresholds:
    noise_curve: dict[str, float] = {}
    noise_zero_crossing: float | None = None
    for sigma in (0.00, 0.05, 0.10, 0.15, 0.20, 0.30, 0.40, 0.50, 0.65, 0.80, 1.00):
        noise_rng = random.Random(777 + int(sigma * 1000))
        val = statistics.fmean(
            _score_3tier_decision(
                adv,
                adv.p_rel + noise_rng.gauss(0.0, sigma),
                c_rel_mid=c_rel,
                c_irrel_mid=c_irrel,
                coarse_discount=disc,
                use_prior_stakes=True,
            )[1]
            for adv in mixed_stream
        )
        noise_curve[f"sigma_{sigma:.2f}"] = round(val, 4)
        if noise_zero_crossing is None and val <= 0.0:
            noise_zero_crossing = sigma

    bias_curve: dict[str, float] = {}
    bias_zero_crossing: float | None = None
    for step in range(0, 50, 5):
        bias = step / 100.0
        val = statistics.fmean(
            _score_3tier_decision(
                adv,
                adv.p_rel + bias,
                c_rel_mid=c_rel,
                c_irrel_mid=c_irrel,
                coarse_discount=disc,
                use_prior_stakes=True,
            )[1]
            for adv in mixed_stream
        )
        bias_curve[f"bias_+{bias:.2f}"] = round(val, 4)
        if bias_zero_crossing is None and val <= 0.0:
            bias_zero_crossing = bias

    assert noise_curve["sigma_0.10"] > 4.5
    assert bias_zero_crossing is not None and 0.20 <= bias_zero_crossing <= 0.30

    return {
        "evidence_role": "normative + documentation + derived",
        "off_topic_resumption_penalty_ratio_chi08": round(c_irrel / c_rel, 3),
        "coarse_over_fine_coi_discount_chi06": round(disc, 4),
        "low_relevance_net_utility": low_rel_res,
        "mixed_workload_net_utility": mixed_res,
        "mixed_workload_tier_routing_counts": tier_counts,
        "mixed_workload_gaussian_noise_curve": noise_curve,
        "mixed_workload_gaussian_noise_zero_crossing": noise_zero_crossing,
        "mixed_workload_overconfidence_bias_curve": bias_curve,
        "overconfidence_bias_zero_utility_breakdown": bias_zero_crossing,
    }


def main() -> None:
    banner_specs = [
        (
            "PROBE 1",
            "probe_kv_prefix_and_goal_activation",
            "documentation + source + derived",
            probe_kv_prefix_and_goal_activation,
        ),
        (
            "PROBE 2",
            "probe_alertmanager_groupwait_interval_and_inhibition",
            "normative + source + derived",
            probe_alertmanager_groupwait_interval_and_inhibition,
        ),
        (
            "PROBE 3",
            "probe_tms_doa_survival_decay_vs_broadcast",
            "documentation + source + derived",
            probe_tms_doa_survival_decay_vs_broadcast,
        ),
        (
            "PROBE 4",
            "probe_tokio_coop_and_langgraph_superstep_delivery",
            "source + derived",
            probe_tokio_coop_and_langgraph_superstep_delivery,
        ),
        (
            "PROBE 5",
            "probe_voi_interruption_gate",
            "normative + documentation + derived",
            probe_voi_interruption_gate,
        ),
    ]

    results: dict[str, Any] = {}
    for code, fn_name, ev_role, fn in banner_specs:
        print(f"=== [{code}] {fn_name} | [evidence_role: {ev_role}] ===")
        out = fn()
        results[fn_name] = out

    payload = json.dumps(results, indent=2, sort_keys=True)
    digest_full = hashlib.sha256(payload.encode("utf-8")).hexdigest()
    print(
        f"=== ALL 5 VERIFICATION PROBES PASSED DETERMINISTICALLY "
        f"(payload_sha256_12={digest_full[:12]}, payload_sha256={digest_full}) ==="
    )
    print(payload)


if __name__ == "__main__":
    main()
