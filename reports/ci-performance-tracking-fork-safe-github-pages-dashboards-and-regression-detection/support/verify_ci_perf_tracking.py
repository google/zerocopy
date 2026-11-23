#!/usr/bin/env python3
"""Deterministic verification suite for CI performance tracking, orphan-branch
storage scaling, statistical regression detection, Linux exec_mmap ru_maxrss
contamination, and fork-safe static dashboard security invariants.

Requires Python 3.10+ standard library only. Produces deterministic,
PYTHONHASHSEED-independent JSON output.
"""

from __future__ import annotations

import gzip
import json
import math
import mmap
import os
import random
import re
import statistics
import subprocess
import sys


def probe_1_storage_scaling() -> dict[str, object]:
    """Compare wire and gzip sizes across 2,000 commits x 60 metrics."""
    n_commits = 2000
    n_metrics = 60

    gab_entries = []
    jsonl_lines = []
    col_commits = []
    col_series: dict[str, list[float]] = {
        f"anneal/verify/metric_{m:02d}": [] for m in range(n_metrics)
    }

    for c in range(n_commits):
        sha = f"{c + 1:040x}"
        tree_sha = f"{c + 100001:040x}"
        ts = 1795000000 + c * 3600
        msg = f"[anneal][theory] Optimize module elaboration step {c} (#4{c % 900 + 100})"
        benches = []
        row_metrics: dict[str, float] = {}
        for m in range(n_metrics):
            key = f"anneal/verify/metric_{m:02d}"
            val = round(400.0 + (m * 17.3) + (c % 11) * 1.2, 2)
            benches.append({"name": key, "unit": "ms", "value": val})
            row_metrics[key] = val
            col_series[key].append(val)

        gab_entries.append(
            {
                "commit": {
                    "author": {
                        "email": "author@example.com",
                        "name": "Example Author",
                        "username": "author",
                    },
                    "committer": {
                        "email": "noreply@github.com",
                        "name": "GitHub",
                        "username": "web-flow",
                    },
                    "distinct": True,
                    "id": sha,
                    "message": msg,
                    "timestamp": "2026-11-23T00:00:00Z",
                    "tree_id": tree_sha,
                    "url": f"https://github.com/example/repo/commit/{sha}",
                },
                "date": ts * 1000,
                "tool": "customSmallerIsBetter",
                "benches": benches,
            }
        )
        jsonl_lines.append(
            json.dumps(
                {"v": 1, "sha": sha, "ts": ts, "title": msg, "metrics": row_metrics},
                separators=(",", ":"),
                sort_keys=True,
            )
        )
        col_commits.append([sha[:12], sha, ts, msg])

    gab_payload = {
        "lastUpdate": 1795000000000,
        "repoUrl": "https://github.com/example/repo",
        "entries": {"Anneal": gab_entries},
    }
    gab_bytes = (
        "window.BENCHMARK_DATA = " + json.dumps(gab_payload, indent=2, sort_keys=True)
    ).encode("utf-8")
    jsonl_bytes = ("\n".join(jsonl_lines) + "\n").encode("utf-8")
    col_payload = {
        "schema_version": 1,
        "commits": col_commits,
        "metrics": {
            f"anneal/verify/metric_{m:02d}": {"unit": "ms", "direction": "lower_is_better"}
            for m in range(n_metrics)
        },
        "series": col_series,
    }
    col_bytes = json.dumps(col_payload, separators=(",", ":"), sort_keys=True).encode(
        "utf-8"
    )

    gab_gz = len(gzip.compress(gab_bytes, compresslevel=9, mtime=0))
    jsonl_gz = len(gzip.compress(jsonl_bytes, compresslevel=9, mtime=0))
    col_gz = len(gzip.compress(col_bytes, compresslevel=9, mtime=0))

    assert len(gab_bytes) > 3 * len(jsonl_bytes)
    assert len(gab_bytes) > 14 * len(col_bytes)
    assert len(jsonl_bytes) > 3 * len(col_bytes)
    assert gab_gz > 10 * jsonl_gz
    assert jsonl_gz > col_gz

    return {
        "points_total": n_commits * n_metrics,
        "gab_data_js_raw_bytes": len(gab_bytes),
        "gab_data_js_gzip_bytes": gab_gz,
        "append_jsonl_raw_bytes": len(jsonl_bytes),
        "append_jsonl_gzip_bytes": jsonl_gz,
        "columnar_json_raw_bytes": len(col_bytes),
        "columnar_json_gzip_bytes": col_gz,
        "raw_ratio_gab_to_columnar": round(len(gab_bytes) / len(col_bytes), 2),
        "gzip_ratio_gab_to_columnar": round(gab_gz / col_gz, 2),
    }


def _mad_sigma(window: list[float], med: float) -> float:
    mad = statistics.median([abs(x - med) for x in window])
    return max(1.4826 * mad, 0.01 * med)


def _iqr_fence(window: list[float]) -> float:
    deltas = sorted(
        abs(window[i] - window[i - 1]) / window[i - 1] for i in range(1, len(window))
    )
    q1 = deltas[len(deltas) // 4]
    q3 = deltas[(3 * len(deltas)) // 4]
    return max(0.05, q3 + 3.0 * (q3 - q1))


def _sample_runner(rng: random.Random, true_ms: float, sigma: float) -> float:
    val = true_ms * math.exp(rng.gauss(0.0, sigma))
    if rng.random() < 0.03:
        val *= rng.uniform(1.25, 1.55)
    return val


def probe_2_regression_detectors() -> dict[str, object]:
    """Evaluate 6 regression rules under log-normal noise + 3% noisy-neighbor spikes."""
    rng = random.Random(20261123)
    window_len = 25
    trials = 500
    null_steps = 100
    step_ratio = 1.15

    results: dict[str, dict[str, dict[str, float]]] = {}
    rule_names = (
        "D1_gab_adjacent_ratio",
        "D2_iqr_fence_k1",
        "D3_parametric_mean_sd_k1",
        "D4_k3_median_mad_1pt",
        "D5_k1_trailing3_median_mad",
        "D6_k3_median_mad_2step",
    )

    for sigma in (0.03, 0.08, 0.12):
        fp = {k: 0 for k in rule_names}
        tp = {k: 0 for k in rule_names}

        for _ in range(trials):
            s1 = [
                _sample_runner(rng, 1000.0, sigma)
                for _ in range(window_len + null_steps)
            ]
            s3 = [
                statistics.median(
                    [_sample_runner(rng, 1000.0, sigma) for _ in range(3)]
                )
                for _ in range(window_len + null_steps)
            ]
            prev_z3 = 0.0

            for t in range(window_len, window_len + null_steps):
                w1 = s1[t - window_len : t]
                med1 = statistics.median(w1)
                mean1 = statistics.fmean(w1)
                sd1 = max(statistics.stdev(w1), 0.01 * mean1)

                if s1[t] / s1[t - 1] > 1.15:
                    fp["D1_gab_adjacent_ratio"] += 1
                if (s1[t] - med1) / med1 > _iqr_fence(w1):
                    fp["D2_iqr_fence_k1"] += 1
                if (s1[t] - mean1) / sd1 > 3.5 and (s1[t] - mean1) / mean1 > 0.08:
                    fp["D3_parametric_mean_sd_k1"] += 1

                base1 = s1[t - window_len : t - 2]
                bmed1 = statistics.median(base1)
                bsig1 = _mad_sigma(base1, bmed1)
                tail3 = statistics.median(s1[t - 2 : t + 1])
                if (
                    (tail3 - bmed1) / (0.7236 * bsig1) > 4.2
                    and (tail3 - bmed1) / bmed1 > 0.08
                ):
                    fp["D5_k1_trailing3_median_mad"] += 1

                w3 = s3[t - window_len : t]
                med3 = statistics.median(w3)
                sig3 = _mad_sigma(w3, med3)
                z3 = (s3[t] - med3) / sig3
                if z3 > 4.2 and (s3[t] - med3) / med3 > 0.08:
                    fp["D4_k3_median_mad_1pt"] += 1
                if z3 > 3.5 and prev_z3 > 3.5 and (s3[t] - med3) / med3 > 0.08:
                    fp["D6_k3_median_mad_2step"] += 1
                prev_z3 = z3

            # Permanent +15% regression step
            w1 = [_sample_runner(rng, 1000.0, sigma) for _ in range(window_len)]
            y1 = [_sample_runner(rng, 1000.0 * step_ratio, sigma) for _ in range(3)]
            med1 = statistics.median(w1)
            mean1 = statistics.fmean(w1)
            sd1 = max(statistics.stdev(w1), 0.01 * mean1)

            if y1[0] / w1[-1] > 1.15:
                tp["D1_gab_adjacent_ratio"] += 1
            if (y1[0] - med1) / med1 > _iqr_fence(w1):
                tp["D2_iqr_fence_k1"] += 1
            if (y1[0] - mean1) / sd1 > 3.5 and (y1[0] - mean1) / mean1 > 0.08:
                tp["D3_parametric_mean_sd_k1"] += 1
            tail3 = statistics.median(y1)
            if (
                (tail3 - med1) / (0.7236 * _mad_sigma(w1, med1)) > 4.2
                and (tail3 - med1) / med1 > 0.08
            ):
                tp["D5_k1_trailing3_median_mad"] += 1

            w3 = [
                statistics.median(
                    [_sample_runner(rng, 1000.0, sigma) for _ in range(3)]
                )
                for _ in range(window_len)
            ]
            y3 = [
                statistics.median(
                    [
                        _sample_runner(rng, 1000.0 * step_ratio, sigma)
                        for _ in range(3)
                    ]
                )
                for _ in range(2)
            ]
            med3 = statistics.median(w3)
            z3_0 = (y3[0] - med3) / _mad_sigma(w3, med3)
            if z3_0 > 4.2 and (y3[0] - med3) / med3 > 0.08:
                tp["D4_k3_median_mad_1pt"] += 1
            w3_next = w3[1:] + [y3[0]]
            med3_next = statistics.median(w3_next)
            z3_1 = (y3[1] - med3_next) / _mad_sigma(w3_next, med3_next)
            if z3_0 > 3.5 and z3_1 > 3.5 and (y3[1] - med3_next) / med3_next > 0.08:
                tp["D6_k3_median_mad_2step"] += 1

        total_null = trials * null_steps
        sigma_key = f"sigma_{sigma:.2f}"
        results[sigma_key] = {
            k: {
                "fpr_per_100_commits": round(100.0 * fp[k] / total_null, 2),
                "tpr_pct_on_15pct_step": round(100.0 * tp[k] / trials, 1),
            }
            for k in rule_names
        }

    # Verify arithmetic-mean percent-change asymmetry vs geometric-mean symmetry
    ratios = [2.0, 0.5]
    arith_pct_ab = round(100.0 * statistics.fmean(r - 1.0 for r in ratios), 4)
    arith_pct_ba = round(100.0 * statistics.fmean((1.0 / r) - 1.0 for r in ratios), 4)
    geo_ab = round(math.exp(statistics.fmean(math.log(r) for r in ratios)), 6)
    geo_ba = round(math.exp(statistics.fmean(math.log(1.0 / r) for r in ratios)), 6)
    assert arith_pct_ab == 25.0 and arith_pct_ba == 25.0
    assert geo_ab == 1.0 and geo_ba == 1.0

    return {
        "detector_matrix": results,
        "summary_mean_symmetry": {
            "arith_mean_pct_change_forward": arith_pct_ab,
            "arith_mean_pct_change_inverse": arith_pct_ba,
            "geomean_ratio_forward": geo_ab,
            "geomean_ratio_inverse": geo_ba,
        },
    }


def _model_linux_exec_maxrss(
    *,
    parent_live_rss_kib: int,
    parent_hiwater_rss_kib: int,
    child_true_rss_kib: int,
    mode: str,
    shim_rss_kib: int = 1024,
) -> int:
    """Exact Linux fs/exec.c:918 (`exec_mm_put_old`) + kernel/fork.c:1554,1598 model."""
    assert parent_hiwater_rss_kib >= parent_live_rss_kib
    if mode == "vfork_posix_spawn":
        # CLONE_VM shares parent mm_struct; exec_mm_put_old folds old_mm->hiwater_rss
        old_mm_peak = max(parent_hiwater_rss_kib, parent_live_rss_kib)
        return max(old_mm_peak, child_true_rss_kib)
    if mode == "fork_exec":
        # dup_mm sets child old_mm->hiwater_rss = get_mm_rss(parent_mm) at fork time
        old_mm_peak = parent_live_rss_kib
        return max(old_mm_peak, child_true_rss_kib)
    if mode == "fresh_exec_shim":
        # First exec creates a tiny shim mm_struct; second fork+exec sees only shim_rss_kib
        return max(shim_rss_kib, child_true_rss_kib)
    raise ValueError(f"unknown mode: {mode}")


def probe_3_linux_maxrss_accounting() -> dict[str, object]:
    """Verify Linux exec_mm_put_old ru_maxrss contamination model & live Linux behavior."""
    mapped_fork = _model_linux_exec_maxrss(
        parent_live_rss_kib=131072,
        parent_hiwater_rss_kib=131072,
        child_true_rss_kib=1024,
        mode="fork_exec",
    )
    unmapped_fork = _model_linux_exec_maxrss(
        parent_live_rss_kib=8192,
        parent_hiwater_rss_kib=131072,
        child_true_rss_kib=1024,
        mode="fork_exec",
    )
    unmapped_vfork = _model_linux_exec_maxrss(
        parent_live_rss_kib=8192,
        parent_hiwater_rss_kib=131072,
        child_true_rss_kib=1024,
        mode="vfork_posix_spawn",
    )
    shim_grandchild = _model_linux_exec_maxrss(
        parent_live_rss_kib=131072,
        parent_hiwater_rss_kib=131072,
        child_true_rss_kib=1024,
        mode="fresh_exec_shim",
        shim_rss_kib=1536,
    )
    assert mapped_fork == 131072
    assert unmapped_fork == 8192
    assert unmapped_vfork == 131072
    assert shim_grandchild == 1536

    # Verify live kernel behavior when running on Linux with /bin/true available
    if sys.platform == "linux" and os.path.exists("/bin/true") and hasattr(os, "wait4"):
        child_code = (
            "import mmap, os, subprocess\n"
            "b = mmap.mmap(-1, 64*1024*1024, flags=mmap.MAP_PRIVATE, "
            "prot=mmap.PROT_READ|mmap.PROT_WRITE)\n"
            "for off in range(0, 64*1024*1024, 4096): b[off] = 1\n"
            "pid = os.fork()\n"
            "if pid == 0: os.execv('/bin/true', ['/bin/true'])\n"
            "_, _, ru_f_map = os.wait4(pid, 0)\n"
            "b.close()\n"
            "pid2 = os.fork()\n"
            "if pid2 == 0: os.execv('/bin/true', ['/bin/true'])\n"
            "_, _, ru_f_unmap = os.wait4(pid2, 0)\n"
            "p = subprocess.Popen(['/bin/true'])\n"
            "_, _, ru_vf_unmap = os.wait4(p.pid, 0)\n"
            "assert ru_f_map.ru_maxrss >= 60000, ru_f_map.ru_maxrss\n"
            "assert ru_f_unmap.ru_maxrss < 32000, ru_f_unmap.ru_maxrss\n"
            "assert ru_vf_unmap.ru_maxrss >= 60000, ru_vf_unmap.ru_maxrss\n"
        )
        subprocess.run([sys.executable, "-I", "-B", "-c", child_code], check=True)

    return {
        "model_128mib_parent_1mib_child_kib": {
            "fork_exec_while_mapped": mapped_fork,
            "fork_exec_after_munmap": unmapped_fork,
            "vfork_posix_spawn_after_munmap": unmapped_vfork,
            "fresh_exec_shim_while_mapped": shim_grandchild,
        },
        "invariants_verified": True,
    }


def _safe_inline_json_script(payload: object) -> str:
    raw = json.dumps(payload, separators=(",", ":"), sort_keys=True)
    return (
        raw.replace("<", "\\u003c")
        .replace(">", "\\u003e")
        .replace("&", "\\u0026")
        .replace("\u2028", "\\u2028")
        .replace("\u2029", "\\u2029")
    )


def probe_4_security_and_html_invariants() -> dict[str, object]:
    """Verify HTML5 </script> breakout prevention and zero-CDN dashboard invariants."""
    hostile_commit_title = "Fix parser </script><script>alert(1)</script> & \u2028 edge"
    encoded = _safe_inline_json_script({"title": hostile_commit_title})
    html_doc = (
        "<!doctype html><html><head><meta charset='utf-8'></head><body>"
        f"<script id='perf-data' type='application/json'>{encoded}</script>"
        "<script>'use strict';</script></body></html>"
    )
    assert "</script><script>alert" not in html_doc
    assert re.search(r"(?:src|href)\s*=\s*['\"]https?://", html_doc, re.I) is None
    decoded = json.loads(encoded)
    assert decoded["title"] == hostile_commit_title

    return {
        "script_breakout_neutralized": True,
        "roundtrip_exact": True,
        "external_cdn_refs": 0,
    }


def main() -> int:
    summary = {
        "suite": "ci-performance-tracking-verification/1",
        "probe_1_storage_scaling": probe_1_storage_scaling(),
        "probe_2_regression_detectors": probe_2_regression_detectors(),
        "probe_3_linux_maxrss_accounting": probe_3_linux_maxrss_accounting(),
        "probe_4_security_and_html_invariants": probe_4_security_and_html_invariants(),
    }
    sys.stdout.write(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
