#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Compile `anneal/records.jsonl` into a zero-CDN static HTML/JSON dashboard."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
from typing import Any

_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

import anneal_ci_lib
import perf_tracking

DASHBOARD_SCHEMA = "anneal-perf-dashboard/v1"
DEFAULT_REPO_URL = "https://github.com/google/zerocopy"
REPO_URL_RE = re.compile(
    r"^https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$"
)


def validate_repo_url(repo_url: str) -> str:
    """Strictly validate GitHub repository URL before embedding in HTML/JSON."""
    cleaned = repo_url.rstrip("/")
    if not REPO_URL_RE.match(cleaned):
        raise perf_tracking.ValidationError(
            f"invalid GitHub repo_url {repo_url!r}; expected {REPO_URL_RE.pattern}"
        )
    owner, repo = cleaned[len("https://github.com/") :].split("/", 1)
    if owner in (".", "..") or repo in (".", ".."):
        raise perf_tracking.ValidationError(
            f"invalid GitHub owner/repo path segment in {repo_url!r}"
        )
    return cleaned


def serialize_inline_json(data: Any) -> str:
    """Serialize JSON safely for embedding inside HTML5 `<script>` tags.

    Escapes `<`, `>`, `&`, `U+2028`, and `U+2029` so arbitrary commit subjects
    cannot break out of `<script type="application/json">`.
    """
    raw = json.dumps(data, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return (
        raw.replace("&", "\\u0026")
        .replace("<", "\\u003c")
        .replace(">", "\\u003e")
        .replace("\u2028", "\\u2028")
        .replace("\u2029", "\\u2029")
    )


def build_dashboard_bundle(
    records: list[dict[str, Any]],
    budgets_cfg: dict[str, Any] | None = None,
    *,
    profile: str | None = None,
    repo_url: str = DEFAULT_REPO_URL,
    max_commits: int = 1000,
    generated_at: str | None = None,
) -> dict[str, Any]:
    """Compile `anneal-perf-record/v1` history into `anneal-perf-dashboard/v1`."""
    safe_repo_url = validate_repo_url(repo_url)
    if max_commits < 1:
        raise perf_tracking.ValidationError("max_commits must be >= 1")

    if not records:
        target_profile = profile or "github-ubuntu-24.04-x86_64"
        return {
            "schema": DASHBOARD_SCHEMA,
            "repo_url": safe_repo_url,
            "generated_at": generated_at or "1970-01-01T00:00:00Z",
            "profile": target_profile,
            "rolling_policy": dict(perf_tracking.DEFAULT_ROLLING_POLICY),
            "commits": [],
            "metrics": {},
            "series": {},
            "summaries": {
                "category_geomean_vs_prev": {},
                "category_geomean_vs_baseline": {},
            },
            "anomalies": [],
        }

    target_profile = profile or records[-1]["environment"]["profile"]
    filtered = [
        r for r in records if r["environment"]["profile"] == target_profile
    ]
    if len(filtered) > max_commits:
        filtered = filtered[-max_commits:]

    analysis = perf_tracking.analyze_history(
        filtered, budgets_cfg, profile=target_profile
    )
    commits = analysis["commits"]

    all_metric_ids = sorted(
        {metric_id for rec in filtered for metric_id in rec["metrics"].keys()}
    )
    metrics_meta: dict[str, dict[str, Any]] = {}
    series: dict[str, list[float | int | None]] = {}

    for metric_id in all_metric_ids:
        desc = perf_tracking.describe_metric(metric_id)
        if budgets_cfg is not None:
            b_min, b_max = perf_tracking.budget_bounds_for_metric(
                budgets_cfg, metric_id
            )
            if b_max is not None:
                desc["budget_max"] = b_max
            if b_min is not None:
                desc["budget_min"] = b_min
        metrics_meta[metric_id] = desc
        # Columnar alignment invariant: every series has exact length
        # `len(commits)` with `None` for commits missing that metric.
        series[metric_id] = [rec["metrics"].get(metric_id) for rec in filtered]

    rolling = (
        dict(budgets_cfg["rolling"])
        if budgets_cfg is not None
        else dict(perf_tracking.DEFAULT_ROLLING_POLICY)
    )

    ts_default = filtered[-1]["commit"]["timestamp"] if filtered else "1970-01-01T00:00:00Z"
    return {
        "schema": DASHBOARD_SCHEMA,
        "repo_url": safe_repo_url,
        "generated_at": generated_at or ts_default,
        "profile": target_profile,
        "rolling_policy": rolling,
        "commits": commits,
        "metrics": metrics_meta,
        "series": series,
        "summaries": {
            "category_geomean_vs_prev": analysis["category_geomean_vs_prev"],
            "category_geomean_vs_baseline": analysis[
                "category_geomean_vs_baseline"
            ],
        },
        "anomalies": analysis["anomalies"],
    }


_HTML_TEMPLATE = r"""<!DOCTYPE html>
<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->
<html lang="en" data-theme="light">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Anneal Performance Dashboard</title>
<style>
:root {
  --bg: #f6f7f9;
  --surface: #ffffff;
  --surface-alt: #f0f2f6;
  --border: #d8dee6;
  --text: #151922;
  --muted: #596373;
  --accent: #0b57d0;
  --ok: #137333;
  --ok-bg: #e6f4ea;
  --warn: #b06000;
  --warn-bg: #fef7e0;
  --err: #c5221f;
  --err-bg: #fce8e6;
  --band: rgba(11, 87, 208, 0.12);
  --mono: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
  --sans: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
}
[data-theme="dark"] {
  --bg: #0f131a;
  --surface: #171d26;
  --surface-alt: #1f2733;
  --border: #2c3748;
  --text: #e6edf3;
  --muted: #93a1b5;
  --accent: #6ea8fe;
  --ok: #5bb974;
  --ok-bg: rgba(91, 185, 116, 0.14);
  --warn: #f6ad55;
  --warn-bg: rgba(246, 173, 85, 0.14);
  --err: #f28b82;
  --err-bg: rgba(242, 139, 130, 0.15);
  --band: rgba(110, 168, 254, 0.16);
}
* { box-sizing: border-box; }
body {
  margin: 0;
  font-family: var(--sans);
  background: var(--bg);
  color: var(--text);
  line-height: 1.45;
}
a { color: var(--accent); text-decoration: none; }
a:hover { text-decoration: underline; }
.wrap { max-width: 1360px; margin: 0 auto; padding: 20px; }
header {
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: center;
  gap: 12px;
  padding-bottom: 16px;
  border-bottom: 1px solid var(--border);
}
.title-block h1 { margin: 0; font-size: 1.4rem; letter-spacing: -0.01em; }
.meta-row {
  display: flex;
  flex-wrap: wrap;
  gap: 10px;
  margin-top: 6px;
  font-size: 0.85rem;
  color: var(--muted);
}
.pill {
  display: inline-flex;
  align-items: center;
  gap: 6px;
  padding: 3px 9px;
  border-radius: 999px;
  border: 1px solid var(--border);
  background: var(--surface);
  font-size: 0.8rem;
}
.pill.ok { color: var(--ok); background: var(--ok-bg); border-color: transparent; }
.pill.warn { color: var(--warn); background: var(--warn-bg); border-color: transparent; }
.pill.err { color: var(--err); background: var(--err-bg); border-color: transparent; }
.header-actions { display: flex; gap: 8px; align-items: center; }
button, select, input {
  font: inherit;
  color: var(--text);
  background: var(--surface);
  border: 1px solid var(--border);
  border-radius: 6px;
  padding: 6px 10px;
}
button { cursor: pointer; }
button:hover { border-color: var(--accent); }
button.active {
  background: var(--accent);
  color: #ffffff;
  border-color: var(--accent);
}
.kpi-grid {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(210px, 1fr));
  gap: 12px;
  margin: 18px 0;
}
.kpi-card {
  background: var(--surface);
  border: 1px solid var(--border);
  border-radius: 8px;
  padding: 12px 14px;
}
.kpi-title { font-size: 0.78rem; color: var(--muted); text-transform: uppercase; letter-spacing: 0.04em; }
.kpi-val { font-size: 1.35rem; font-weight: 700; margin-top: 4px; font-family: var(--mono); }
.kpi-sub { font-size: 0.8rem; color: var(--muted); margin-top: 2px; }
.toolbar {
  display: flex;
  flex-wrap: wrap;
  gap: 10px;
  align-items: center;
  background: var(--surface);
  border: 1px solid var(--border);
  border-radius: 8px;
  padding: 12px;
  margin-bottom: 18px;
}
.toolbar input[type="search"] { min-width: 240px; flex: 1 1 240px; }
.btn-group { display: flex; flex-wrap: wrap; gap: 6px; }
.detail-panel {
  background: var(--surface);
  border: 1px solid var(--border);
  border-radius: 10px;
  padding: 16px;
  margin-bottom: 20px;
}
.detail-head {
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: center;
  gap: 10px;
  margin-bottom: 10px;
}
.detail-title { font-size: 1.05rem; font-weight: 600; }
.detail-id { font-family: var(--mono); font-size: 0.8rem; color: var(--muted); }
.chart-wrap { position: relative; width: 100%; height: 320px; }
canvas { width: 100%; height: 100%; display: block; cursor: crosshair; }
.tooltip {
  position: absolute;
  pointer-events: none;
  background: var(--surface);
  border: 1px solid var(--border);
  border-radius: 6px;
  padding: 8px 10px;
  font-size: 0.78rem;
  box-shadow: 0 6px 20px rgba(0, 0, 0, 0.16);
  display: none;
  z-index: 5;
  max-width: 340px;
}
.legend { display: flex; flex-wrap: wrap; gap: 12px; font-size: 0.78rem; margin-top: 8px; color: var(--muted); }
.legend-item { display: inline-flex; align-items: center; gap: 6px; }
.swatch { width: 12px; height: 3px; display: inline-block; border-radius: 2px; }
.spark-grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(290px, 1fr));
  gap: 12px;
  margin-bottom: 22px;
}
.spark-card {
  background: var(--surface);
  border: 1px solid var(--border);
  border-radius: 8px;
  padding: 12px;
  cursor: pointer;
  transition: border-color 0.15s ease;
}
.spark-card:hover, .spark-card.selected { border-color: var(--accent); }
.spark-top { display: flex; justify-content: space-between; align-items: flex-start; gap: 8px; }
.spark-label { font-size: 0.88rem; font-weight: 600; }
.spark-id { font-family: var(--mono); font-size: 0.72rem; color: var(--muted); word-break: break-all; }
.spark-val-row { display: flex; justify-content: space-between; align-items: baseline; margin: 8px 0 4px; }
.spark-val { font-family: var(--mono); font-size: 1.15rem; font-weight: 700; }
.spark-delta { font-family: var(--mono); font-size: 0.8rem; }
.spark-svg { width: 100%; height: 48px; display: block; }
.table-wrap {
  background: var(--surface);
  border: 1px solid var(--border);
  border-radius: 8px;
  overflow-x: auto;
}
table { width: 100%; border-collapse: collapse; font-size: 0.84rem; }
th, td { padding: 8px 10px; border-bottom: 1px solid var(--border); text-align: left; }
th { background: var(--surface-alt); font-weight: 600; }
td.num, th.num { text-align: right; font-family: var(--mono); }
.empty { padding: 28px; text-align: center; color: var(--muted); }
@media (max-width: 720px) {
  .wrap { padding: 12px; }
  .chart-wrap { height: 240px; }
}
</style>
</head>
<body>
<div class="wrap">
  <header>
    <div class="title-block">
      <h1>Anneal Performance Dashboard</h1>
      <div class="meta-row" id="header-meta"></div>
    </div>
    <div class="header-actions">
      <button id="theme-toggle" type="button">Dark theme</button>
      <button id="download-json" type="button">Download JSON</button>
    </div>
  </header>

  <section class="kpi-grid" id="kpi-grid"></section>

  <section class="toolbar">
    <input id="search-input" type="search" placeholder="Filter metrics (press / to focus)...">
    <div class="btn-group" id="category-pills"></div>
    <div class="btn-group" id="window-buttons"></div>
    <select id="baseline-select" aria-label="Baseline comparator"></select>
  </section>

  <section class="detail-panel" id="detail-panel">
    <div class="detail-head">
      <div>
        <div class="detail-title" id="detail-title">Select a metric</div>
        <div class="detail-id" id="detail-id"></div>
      </div>
      <div class="btn-group">
        <button id="overlay-toggle" type="button">Group Sibling Overlay: Off</button>
      </div>
    </div>
    <div class="chart-wrap">
      <canvas id="detail-canvas"></canvas>
      <div class="tooltip" id="chart-tooltip"></div>
    </div>
    <div class="legend" id="detail-legend"></div>
  </section>

  <section class="spark-grid" id="spark-grid"></section>

  <section class="table-wrap">
    <table>
      <thead>
        <tr>
          <th>Metric</th>
          <th>Category</th>
          <th class="num">Current</th>
          <th class="num">Baseline</th>
          <th class="num">Delta</th>
          <th class="num">Budget Max</th>
          <th>Status</th>
        </tr>
      </thead>
      <tbody id="comparison-tbody"></tbody>
    </table>
  </section>
</div>

<script id="anneal-perf-inline-data" type="application/json">__ANNEAL_INLINE_JSON__</script>
<script>
(function () {
  "use strict";

  var REPO_URL_RE = /^https:\/\/github\.com\/[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/;
  var SHA_RE = /^[0-9a-f]{40}$/;
  var PALETTE = ["#0b57d0", "#c5221f", "#137333", "#b06000", "#7b1fa2", "#00838f"];
  var CAT_LABELS = {
    verify: "Verify",
    theory_elab: "Theory Cold Elab",
    memory_rss: "Peak RSS",
    artifact_size: "Artifact Sizes",
    zerocopy_proofs: "Zerocopy Proofs"
  };

  function isValidRepoUrl(url) {
    var m = REPO_URL_RE.exec(url || "");
    if (!m) return false;
    var tail = m[0].split("/");
    var owner = tail[tail.length - 2];
    var repo = tail[tail.length - 1];
    return owner !== "." && owner !== ".." && repo !== "." && repo !== "..";
  }

  var rawEl = document.getElementById("anneal-perf-inline-data");
  var data = JSON.parse(rawEl ? rawEl.textContent : "{}");
  var commits = Array.isArray(data.commits) ? data.commits : [];
  var metrics = data.metrics || {};
  var seriesMap = data.series || {};
  var anomalies = Array.isArray(data.anomalies) ? data.anomalies : [];
  var rolling = data.rolling_policy || { window: 25, min_history: 5, mad_floor_rel: 0.015 };
  var safeRepoUrl = isValidRepoUrl(data.repo_url) ? data.repo_url : "";

  var state = {
    query: "",
    category: "all",
    windowSize: 50,
    baselineMode: "rolling",
    selectedMetric: Object.keys(metrics).sort()[0] || "",
    overlaySiblings: false,
    theme: "light"
  };

  try {
    var savedTheme = localStorage.getItem("anneal-perf-theme");
    if (savedTheme === "dark" || savedTheme === "light") {
      state.theme = savedTheme;
    } else if (window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches) {
      state.theme = "dark";
    }
  } catch (e) {}

  function applyTheme() {
    document.documentElement.setAttribute("data-theme", state.theme);
    var btn = document.getElementById("theme-toggle");
    if (btn) btn.textContent = state.theme === "dark" ? "Light theme" : "Dark theme";
  }

  function clearEl(el) {
    while (el.firstChild) el.removeChild(el.firstChild);
  }

  function mk(tag, cls, text) {
    var el = document.createElement(tag);
    if (cls) el.className = cls;
    if (text !== undefined && text !== null) el.textContent = String(text);
    return el;
  }

  function safeCommitHref(sha) {
    if (!safeRepoUrl || !SHA_RE.test(sha || "")) return "";
    return safeRepoUrl + "/commit/" + sha;
  }

  function formatValue(val, unit) {
    if (val === null || val === undefined || !Number.isFinite(val)) return "-";
    if (unit === "ms") {
      return val >= 1000 ? (val / 1000).toFixed(2) + " s" : val.toFixed(1) + " ms";
    }
    if (unit === "KiB") {
      return val >= 1024 ? (val / 1024).toFixed(1) + " MiB" : Math.round(val) + " KiB";
    }
    if (unit === "B") {
      if (val >= 1048576) return (val / 1048576).toFixed(2) + " MiB";
      if (val >= 1024) return (val / 1024).toFixed(1) + " KiB";
      return Math.round(val) + " B";
    }
    return String(Math.round(val));
  }

  function median(arr) {
    if (!arr.length) return null;
    var s = arr.slice().sort(function (a, b) { return a - b; });
    var mid = Math.floor(s.length / 2);
    return s.length % 2 ? s[mid] : (s[mid - 1] + s[mid]) / 2;
  }

  function sliceRange() {
    if (!commits.length) return [0, 0];
    if (state.windowSize <= 0 || state.windowSize >= commits.length) return [0, commits.length];
    return [commits.length - state.windowSize, commits.length];
  }

  function computeRollingBands(fullSeries) {
    var w = rolling.window || 25;
    var minH = rolling.min_history || 5;
    var floorRel = rolling.mad_floor_rel || 0.015;
    var out = [];
    for (var i = 0; i < fullSeries.length; i++) {
      var hist = [];
      for (var j = Math.max(0, i - w); j < i; j++) {
        if (fullSeries[j] !== null && fullSeries[j] !== undefined) hist.push(fullSeries[j]);
      }
      if (hist.length < minH) {
        out.push(null);
        continue;
      }
      var med = median(hist);
      var devs = hist.map(function (y) { return Math.abs(y - med); });
      var mad = median(devs);
      var sigma = Math.max(1.4826 * mad, floorRel * med, 1e-9);
      out.push({ median: med, sigma: sigma, lo: Math.max(0, med - 2 * sigma), hi: med + 2 * sigma });
    }
    return out;
  }

  function baselineValueFor(metricId) {
    var arr = seriesMap[metricId] || [];
    var idx = arr.length - 1;
    while (idx >= 0 && (arr[idx] === null || arr[idx] === undefined)) idx--;
    if (idx < 0) return { current: null, baseline: null, idx: -1 };
    var current = arr[idx];
    if (state.baselineMode === "prev") {
      var p = idx - 1;
      while (p >= 0 && (arr[p] === null || arr[p] === undefined)) p--;
      return { current: current, baseline: p >= 0 ? arr[p] : null, idx: idx };
    }
    if (state.baselineMode === "rolling") {
      var w = rolling.window || 25;
      var hist = [];
      for (var j = Math.max(0, idx - w); j < idx; j++) {
        if (arr[j] !== null && arr[j] !== undefined) hist.push(arr[j]);
      }
      return { current: current, baseline: hist.length ? median(hist) : null, idx: idx };
    }
    var pinIdx = commits.findIndex(function (c) { return c.sha === state.baselineMode; });
    var pinVal = pinIdx >= 0 ? arr[pinIdx] : null;
    return { current: current, baseline: pinVal, idx: idx };
  }

  function latestStatusFor(metricId) {
    var lastIdx = commits.length - 1;
    var hits = anomalies.filter(function (a) { return a.metric === metricId && a.commit_index === lastIdx; });
    if (hits.some(function (h) { return h.kind === "budget_breach" || h.kind === "confirmed_regression"; })) {
      return hits[0].kind;
    }
    if (hits.length) return hits[0].kind;
    return metrics[metricId] && metrics[metricId].deterministic ? "deterministic" : "ok";
  }

  function filteredMetricIds() {
    var q = state.query.trim().toLowerCase();
    return Object.keys(metrics).sort().filter(function (id) {
      var d = metrics[id];
      if (state.category !== "all" && d.category !== state.category) return false;
      if (q && id.toLowerCase().indexOf(q) === -1 && (d.label || "").toLowerCase().indexOf(q) === -1) return false;
      return true;
    });
  }

  function renderHeader() {
    var meta = document.getElementById("header-meta");
    clearEl(meta);
    if (!commits.length) {
      meta.appendChild(mk("span", "pill", "No commits recorded yet"));
      return;
    }
    var latest = commits[commits.length - 1];
    var href = safeCommitHref(latest.sha);
    if (href) {
      var link = mk("a", "pill", latest.short);
      link.href = href;
      link.target = "_blank";
      link.rel = "noopener noreferrer";
      meta.appendChild(link);
    } else {
      meta.appendChild(mk("span", "pill", latest.short));
    }
    meta.appendChild(mk("span", "pill", latest.timestamp || data.generated_at));
    meta.appendChild(mk("span", "pill", data.profile || ""));
    meta.appendChild(mk("span", "pill", latest.cpu_model || ""));
    var lastIdx = commits.length - 1;
    var activeErrors = anomalies.filter(function (a) {
      return a.commit_index === lastIdx && (a.kind === "confirmed_regression" || a.kind === "budget_breach");
    }).length;
    meta.appendChild(mk("span", activeErrors > 0 ? "pill err" : "pill ok",
      activeErrors > 0 ? activeErrors + " active alert(s)" : "0 regressions"));
  }

  function renderKpis() {
    var grid = document.getElementById("kpi-grid");
    clearEl(grid);
    var geomeans = (data.summaries && data.summaries.category_geomean_vs_baseline) || {};
    var prevMeans = (data.summaries && data.summaries.category_geomean_vs_prev) || {};
    Object.keys(CAT_LABELS).forEach(function (cat) {
      var card = mk("div", "kpi-card");
      card.appendChild(mk("div", "kpi-title", CAT_LABELS[cat]));
      var ratio = geomeans[cat] !== undefined ? geomeans[cat] : prevMeans[cat];
      if (ratio !== undefined && ratio !== null) {
        var pct = ((ratio - 1) * 100).toFixed(2);
        var sign = ratio >= 1 ? "+" : "";
        card.appendChild(mk("div", "kpi-val", ratio.toFixed(3) + "x"));
        card.appendChild(mk("div", "kpi-sub", sign + pct + "% vs baseline"));
      } else {
        card.appendChild(mk("div", "kpi-val", "1.000x"));
        card.appendChild(mk("div", "kpi-sub", "awaiting baseline"));
      }
      grid.appendChild(card);
    });
  }

  function renderControls() {
    var catWrap = document.getElementById("category-pills");
    clearEl(catWrap);
    [["all", "All"]].concat(Object.entries(CAT_LABELS)).forEach(function (pair) {
      var b = mk("button", state.category === pair[0] ? "active" : "", pair[1]);
      b.type = "button";
      b.addEventListener("click", function () { state.category = pair[0]; renderAll(); });
      catWrap.appendChild(b);
    });

    var winWrap = document.getElementById("window-buttons");
    clearEl(winWrap);
    [[50, "Last 50"], [200, "Last 200"], [0, "All"]].forEach(function (pair) {
      var b = mk("button", state.windowSize === pair[0] ? "active" : "", pair[1]);
      b.type = "button";
      b.addEventListener("click", function () { state.windowSize = pair[0]; renderAll(); });
      winWrap.appendChild(b);
    });

    var sel = document.getElementById("baseline-select");
    var prevVal = state.baselineMode;
    clearEl(sel);
    [
      ["rolling", "Baseline: Rolling 25-commit median"],
      ["prev", "Baseline: Previous commit"]
    ].forEach(function (pair) {
      var opt = mk("option", "", pair[1]);
      opt.value = pair[0];
      sel.appendChild(opt);
    });
    commits.slice().reverse().slice(0, 50).forEach(function (c) {
      var opt = mk("option", "", "Pin " + c.short + " (" + (c.subject || "").slice(0, 28) + ")");
      opt.value = c.sha;
      sel.appendChild(opt);
    });
    sel.value = prevVal;
  }

  function buildSparkSvg(values, budgetMax) {
    var ns = "http://www.w3.org/2000/svg";
    var svg = document.createElementNS(ns, "svg");
    svg.setAttribute("viewBox", "0 0 240 48");
    svg.setAttribute("class", "spark-svg");
    var pts = [];
    values.forEach(function (v, idx) {
      if (v !== null && v !== undefined) pts.push([idx, v]);
    });
    if (!pts.length) return svg;
    var ys = pts.map(function (p) { return p[1]; });
    if (budgetMax !== undefined && budgetMax !== null) ys.push(budgetMax);
    var minY = Math.min.apply(null, ys);
    var maxY = Math.max.apply(null, ys);
    if (minY === maxY) { minY = minY * 0.9; maxY = maxY * 1.1 + 1; }
    var denom = Math.max(1, values.length - 1);
    function sx(i) { return (i / denom) * 232 + 4; }
    function sy(v) { return 44 - ((v - minY) / (maxY - minY)) * 40; }

    if (budgetMax !== undefined && budgetMax !== null) {
      var bl = document.createElementNS(ns, "line");
      bl.setAttribute("x1", "4");
      bl.setAttribute("x2", "236");
      var by = sy(budgetMax).toFixed(1);
      bl.setAttribute("y1", by);
      bl.setAttribute("y2", by);
      bl.setAttribute("stroke", "#c5221f");
      bl.setAttribute("stroke-dasharray", "3 3");
      bl.setAttribute("stroke-width", "1");
      svg.appendChild(bl);
    }

    var poly = document.createElementNS(ns, "polyline");
    poly.setAttribute("fill", "none");
    poly.setAttribute("stroke", "currentColor");
    poly.setAttribute("stroke-width", "1.8");
    poly.setAttribute("points", pts.map(function (p) { return sx(p[0]).toFixed(1) + "," + sy(p[1]).toFixed(1); }).join(" "));
    svg.style.color = "var(--accent)";
    svg.appendChild(poly);
    return svg;
  }

  function renderSparkGrid(ids) {
    var grid = document.getElementById("spark-grid");
    clearEl(grid);
    if (!ids.length) {
      grid.appendChild(mk("div", "empty", "No matching metrics."));
      return;
    }
    var range = sliceRange();
    ids.forEach(function (id) {
      var d = metrics[id];
      var card = mk("div", "spark-card" + (id === state.selectedMetric ? " selected" : ""));
      card.addEventListener("click", function () {
        state.selectedMetric = id;
        renderAll();
      });
      var top = mk("div", "spark-top");
      var left = mk("div");
      left.appendChild(mk("div", "spark-label", d.label));
      left.appendChild(mk("div", "spark-id", id));
      top.appendChild(left);
      var status = latestStatusFor(id);
      var pillCls = status === "budget_breach" || status === "confirmed_regression" ? "pill err" :
        status === "candidate_spike" || status === "deterministic_growth" ? "pill warn" : "pill ok";
      top.appendChild(mk("span", pillCls, status));
      card.appendChild(top);

      var cmp = baselineValueFor(id);
      var valRow = mk("div", "spark-val-row");
      valRow.appendChild(mk("div", "spark-val", formatValue(cmp.current, d.unit)));
      if (cmp.current !== null && cmp.baseline !== null && cmp.baseline > 0) {
        var pct = ((cmp.current - cmp.baseline) / cmp.baseline) * 100;
        var deltaEl = mk("div", "spark-delta", (pct >= 0 ? "+" : "") + pct.toFixed(1) + "%");
        if (d.direction === "lower_is_better") {
          deltaEl.style.color = pct > 5 ? "var(--err)" : (pct < -3 ? "var(--ok)" : "var(--muted)");
        }
        valRow.appendChild(deltaEl);
      }
      card.appendChild(valRow);
      var sliced = (seriesMap[id] || []).slice(range[0], range[1]);
      card.appendChild(buildSparkSvg(sliced, d.budget_max));
      grid.appendChild(card);
    });
  }

  function renderDetailChart() {
    var titleEl = document.getElementById("detail-title");
    var idEl = document.getElementById("detail-id");
    var legendEl = document.getElementById("detail-legend");
    var canvas = document.getElementById("detail-canvas");
    var tooltip = document.getElementById("chart-tooltip");
    clearEl(legendEl);

    var id = state.selectedMetric;
    if (!id || !metrics[id]) {
      titleEl.textContent = "No metric selected";
      idEl.textContent = "";
      return;
    }
    var desc = metrics[id];
    titleEl.textContent = desc.label;
    idEl.textContent = id + " (" + desc.unit + ", " + desc.direction + ")";

    var overlayBtn = document.getElementById("overlay-toggle");
    overlayBtn.textContent = "Group Sibling Overlay: " + (state.overlaySiblings ? "On" : "Off");
    overlayBtn.className = state.overlaySiblings ? "active" : "";

    var activeIds = [id];
    if (state.overlaySiblings) {
      Object.keys(metrics).sort().forEach(function (other) {
        if (other !== id && metrics[other].group === desc.group && metrics[other].unit === desc.unit) {
          activeIds.push(other);
        }
      });
    }

    var range = sliceRange();
    var start = range[0];
    var end = range[1];
    var count = Math.max(1, end - start);

    var dpr = window.devicePixelRatio || 1;
    var rect = canvas.getBoundingClientRect();
    var width = Math.max(320, rect.width || 800);
    var height = Math.max(220, rect.height || 320);
    canvas.width = Math.round(width * dpr);
    canvas.height = Math.round(height * dpr);
    var ctx = canvas.getContext("2d");
    ctx.scale(dpr, dpr);
    ctx.clearRect(0, 0, width, height);

    var pad = { left: 68, right: 20, top: 20, bottom: 32 };
    var plotW = width - pad.left - pad.right;
    var plotH = height - pad.top - pad.bottom;

    var allVals = [];
    activeIds.forEach(function (sid) {
      var arr = (seriesMap[sid] || []).slice(start, end);
      arr.forEach(function (v) { if (v !== null && v !== undefined) allVals.push(v); });
    });
    var bands = computeRollingBands(seriesMap[id] || []).slice(start, end);
    bands.forEach(function (b) { if (b) { allVals.push(b.lo, b.hi); } });
    if (desc.budget_max !== undefined && desc.budget_max !== null) allVals.push(desc.budget_max);
    if (!allVals.length) allVals = [0, 1];
    var minY = Math.min.apply(null, allVals);
    var maxY = Math.max.apply(null, allVals);
    if (minY === maxY) { minY = minY * 0.9; maxY = maxY * 1.1 + 1; }
    var spanY = maxY - minY;
    minY = Math.max(0, minY - spanY * 0.05);
    maxY = maxY + spanY * 0.05;

    function xAt(i) {
      if (count <= 1) return pad.left + plotW / 2;
      return pad.left + (i / (count - 1)) * plotW;
    }
    function yAt(v) {
      return pad.top + plotH - ((v - minY) / Math.max(1e-9, maxY - minY)) * plotH;
    }

    var cs = getComputedStyle(document.documentElement);
    var gridColor = cs.getPropertyValue("--border").trim();
    var mutedColor = cs.getPropertyValue("--muted").trim();
    var bandColor = cs.getPropertyValue("--band").trim();

    ctx.strokeStyle = gridColor;
    ctx.fillStyle = mutedColor;
    ctx.font = "11px ui-monospace, monospace";
    for (var g = 0; g <= 4; g++) {
      var gv = minY + ((maxY - minY) * g) / 4;
      var gy = yAt(gv);
      ctx.beginPath();
      ctx.moveTo(pad.left, gy);
      ctx.lineTo(pad.left + plotW, gy);
      ctx.stroke();
      ctx.fillText(formatValue(gv, desc.unit), 6, gy + 4);
    }

    // Rolling Median +/- 2*sigma_MAD band for primary metric.
    ctx.fillStyle = bandColor;
    ctx.beginPath();
    var startedBand = false;
    for (var bi = 0; bi < bands.length; bi++) {
      if (!bands[bi]) continue;
      var bx = xAt(bi);
      var byHi = yAt(bands[bi].hi);
      if (!startedBand) { ctx.moveTo(bx, byHi); startedBand = true; }
      else { ctx.lineTo(bx, byHi); }
    }
    for (var bj = bands.length - 1; bj >= 0; bj--) {
      if (!bands[bj]) continue;
      ctx.lineTo(xAt(bj), yAt(bands[bj].lo));
    }
    if (startedBand) { ctx.closePath(); ctx.fill(); }

    // Hardware SKU shifts & confirmed regression markers.
    for (var ci = 0; ci < end - start; ci++) {
      var globalIdx = start + ci;
      var cObj = commits[globalIdx];
      var isReg = anomalies.some(function (a) {
        return a.metric === id && a.commit_index === globalIdx && a.kind === "confirmed_regression";
      });
      if (cObj && cObj.hw_changed) {
        ctx.save();
        ctx.setLineDash([4, 4]);
        ctx.strokeStyle = "#b06000";
        ctx.beginPath();
        ctx.moveTo(xAt(ci), pad.top);
        ctx.lineTo(xAt(ci), pad.top + plotH);
        ctx.stroke();
        ctx.restore();
      }
      if (isReg) {
        ctx.save();
        ctx.setLineDash([3, 3]);
        ctx.strokeStyle = "#c5221f";
        ctx.beginPath();
        ctx.moveTo(xAt(ci), pad.top);
        ctx.lineTo(xAt(ci), pad.top + plotH);
        ctx.stroke();
        ctx.restore();
      }
    }

    // Budget ceiling line.
    if (desc.budget_max !== undefined && desc.budget_max !== null) {
      ctx.save();
      ctx.setLineDash([6, 4]);
      ctx.strokeStyle = "#c5221f";
      ctx.lineWidth = 1.5;
      var byLine = yAt(desc.budget_max);
      ctx.beginPath();
      ctx.moveTo(pad.left, byLine);
      ctx.lineTo(pad.left + plotW, byLine);
      ctx.stroke();
      ctx.restore();
    }

    // Series lines.
    activeIds.forEach(function (sid, sIdx) {
      var color = PALETTE[sIdx % PALETTE.length];
      var sVals = (seriesMap[sid] || []).slice(start, end);
      ctx.strokeStyle = color;
      ctx.lineWidth = sIdx === 0 ? 2.2 : 1.6;
      ctx.beginPath();
      var penDown = false;
      sVals.forEach(function (val, idx) {
        if (val === null || val === undefined) { penDown = false; return; }
        var px = xAt(idx);
        var py = yAt(val);
        if (!penDown) { ctx.moveTo(px, py); penDown = true; }
        else { ctx.lineTo(px, py); }
      });
      ctx.stroke();

      ctx.fillStyle = color;
      sVals.forEach(function (val, idx) {
        if (val === null || val === undefined) return;
        ctx.beginPath();
        ctx.arc(xAt(idx), yAt(val), sIdx === 0 ? 3 : 2.2, 0, Math.PI * 2);
        ctx.fill();
      });

      var item = mk("span", "legend-item");
      var sw = mk("span", "swatch");
      sw.style.background = color;
      item.appendChild(sw);
      item.appendChild(mk("span", "", sid));
      legendEl.appendChild(item);
    });

    canvas.onmousemove = function (ev) {
      if (!commits.length || end <= start) return;
      var r = canvas.getBoundingClientRect();
      var mx = ev.clientX - r.left;
      var rel = Math.max(0, Math.min(1, (mx - pad.left) / Math.max(1, plotW)));
      var localIdx = Math.round(rel * (end - start - 1));
      var gIdx = start + localIdx;
      var cObj = commits[gIdx];
      if (!cObj) return;
      var val = (seriesMap[id] || [])[gIdx];
      var b = bands[localIdx];
      clearEl(tooltip);
      tooltip.appendChild(mk("div", "", cObj.short + " — " + (cObj.subject || "")));
      tooltip.appendChild(mk("div", "", "Value: " + formatValue(val, desc.unit)));
      if (b && val !== null && val !== undefined) {
        var z = ((val - b.median) / b.sigma).toFixed(2);
        var pct = (((val - b.median) / Math.max(b.median, 1e-9)) * 100).toFixed(1);
        tooltip.appendChild(mk("div", "", "vs median: " + (pct >= 0 ? "+" : "") + pct + "% (z=" + z + ")"));
      }
      tooltip.appendChild(mk("div", "", "CPU: " + (cObj.cpu_model || "")));
      tooltip.style.display = "block";
      tooltip.style.left = Math.min(r.width - 260, Math.max(8, xAt(localIdx) + 12)) + "px";
      tooltip.style.top = "14px";
    };
    canvas.onmouseleave = function () { tooltip.style.display = "none"; };
    canvas.onclick = function (ev) {
      if (!commits.length || end <= start) return;
      var r = canvas.getBoundingClientRect();
      var rel = Math.max(0, Math.min(1, (ev.clientX - r.left - pad.left) / Math.max(1, plotW)));
      var gIdx = start + Math.round(rel * (end - start - 1));
      var href = safeCommitHref(commits[gIdx] && commits[gIdx].sha);
      if (href) window.open(href, "_blank", "noopener,noreferrer");
    };
  }

  function renderTable(ids) {
    var tbody = document.getElementById("comparison-tbody");
    clearEl(tbody);
    ids.forEach(function (id) {
      var d = metrics[id];
      var cmp = baselineValueFor(id);
      var tr = mk("tr");
      var tdName = mk("td");
      var btn = mk("button", "", id);
      btn.type = "button";
      btn.style.fontFamily = "var(--mono)";
      btn.style.fontSize = "0.78rem";
      btn.addEventListener("click", function () { state.selectedMetric = id; renderAll(); });
      tdName.appendChild(btn);
      tr.appendChild(tdName);
      tr.appendChild(mk("td", "", d.category));
      tr.appendChild(mk("td", "num", formatValue(cmp.current, d.unit)));
      tr.appendChild(mk("td", "num", formatValue(cmp.baseline, d.unit)));
      var deltaStr = "-";
      if (cmp.current !== null && cmp.baseline !== null && cmp.baseline > 0) {
        var p = ((cmp.current - cmp.baseline) / cmp.baseline) * 100;
        deltaStr = (p >= 0 ? "+" : "") + p.toFixed(2) + "%";
      }
      tr.appendChild(mk("td", "num", deltaStr));
      tr.appendChild(mk("td", "num", d.budget_max !== undefined ? formatValue(d.budget_max, d.unit) : "-"));
      tr.appendChild(mk("td", "", latestStatusFor(id)));
      tbody.appendChild(tr);
    });
  }

  function renderAll() {
    applyTheme();
    renderHeader();
    renderKpis();
    renderControls();
    var ids = filteredMetricIds();
    if (ids.length && ids.indexOf(state.selectedMetric) === -1) {
      state.selectedMetric = ids[0];
    }
    renderSparkGrid(ids);
    renderDetailChart();
    renderTable(ids);
  }

  document.getElementById("theme-toggle").addEventListener("click", function () {
    state.theme = state.theme === "dark" ? "light" : "dark";
    try { localStorage.setItem("anneal-perf-theme", state.theme); } catch (e) {}
    applyTheme();
    renderDetailChart();
  });

  document.getElementById("search-input").addEventListener("input", function (ev) {
    state.query = ev.target.value || "";
    renderAll();
  });

  document.getElementById("baseline-select").addEventListener("change", function (ev) {
    state.baselineMode = ev.target.value;
    renderAll();
  });

  document.getElementById("overlay-toggle").addEventListener("click", function () {
    state.overlaySiblings = !state.overlaySiblings;
    renderDetailChart();
  });

  document.getElementById("download-json").addEventListener("click", function () {
    var blob = new Blob([JSON.stringify(data, null, 2)], { type: "application/json" });
    var url = URL.createObjectURL(blob);
    var a = document.createElement("a");
    a.href = url;
    a.download = "anneal-perf-data.json";
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  });

  document.addEventListener("keydown", function (ev) {
    if (ev.key === "/" && document.activeElement !== document.getElementById("search-input")) {
      ev.preventDefault();
      document.getElementById("search-input").focus();
    }
  });

  window.addEventListener("resize", renderDetailChart);
  renderAll();
})();
</script>
</body>
</html>
"""


def render_html(bundle: dict[str, Any]) -> str:
    """Embed sanitized inline JSON into the self-contained HTML SPA."""
    inline = serialize_inline_json(bundle)
    return _HTML_TEMPLATE.replace("__ANNEAL_INLINE_JSON__", inline, 1)


def write_dashboard(
    *,
    records_jsonl: Path,
    output_dir: Path,
    budgets_path: Path | None,
    profile: str | None = None,
    repo_url: str = DEFAULT_REPO_URL,
    max_commits: int = 1000,
    generated_at: str | None = None,
) -> dict[str, Any]:
    """Generate `data.json` and `index.html` inside `output_dir` atomically."""
    anneal_ci_lib.ensure_not_symlink(
        output_dir, "output directory", exc_type=perf_tracking.ValidationError
    )
    records = perf_tracking.load_records_jsonl(records_jsonl)
    budgets_cfg = (
        perf_tracking.load_budgets(budgets_path)
        if budgets_path is not None
        else None
    )
    bundle = build_dashboard_bundle(
        records,
        budgets_cfg,
        profile=profile,
        repo_url=repo_url,
        max_commits=max_commits,
        generated_at=generated_at,
    )
    data_json = json.dumps(bundle, sort_keys=True, indent=2) + "\n"
    html_text = render_html(bundle)

    output_dir.mkdir(parents=True, exist_ok=True)
    anneal_ci_lib.atomic_write_text(
        output_dir / "data.json", data_json, exc_type=perf_tracking.ValidationError
    )
    anneal_ci_lib.atomic_write_text(
        output_dir / "index.html", html_text, exc_type=perf_tracking.ValidationError
    )
    return bundle


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "records_pos",
        nargs="?",
        type=Path,
        help="Path to anneal/records.jsonl",
    )
    parser.add_argument(
        "--records",
        type=Path,
        help="Path to anneal/records.jsonl (overrides positional)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("dashboard/anneal"),
    )
    parser.add_argument(
        "--budgets",
        type=Path,
        default=None,
    )
    parser.add_argument("--profile")
    parser.add_argument("--repo-url", default=DEFAULT_REPO_URL)
    parser.add_argument("--max-commits", type=int, default=1000)
    parser.add_argument("--generated-at")

    args = parser.parse_args(argv)
    records_path = args.records or args.records_pos or Path("anneal/records.jsonl")
    budgets_path = args.budgets
    if budgets_path is None and (
        perf_tracking.DEFAULT_BUDGETS_PATH.exists()
        or perf_tracking.DEFAULT_BUDGETS_PATH.is_symlink()
    ):
        budgets_path = perf_tracking.DEFAULT_BUDGETS_PATH
    bundle = write_dashboard(
        records_jsonl=records_path,
        output_dir=args.output_dir,
        budgets_path=budgets_path,
        profile=args.profile,
        repo_url=args.repo_url,
        max_commits=args.max_commits,
        generated_at=args.generated_at,
    )
    print(
        f"Rendered {len(bundle['commits'])} commit(s) and "
        f"{len(bundle['metrics'])} metric(s) into {args.output_dir}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
