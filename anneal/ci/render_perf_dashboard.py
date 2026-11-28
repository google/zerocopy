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


_TEMPLATE_PLACEHOLDER = "__ANNEAL_INLINE_JSON__"


def _load_html_template() -> str:
    """Read the dashboard page, which marks the inline JSON slot once."""
    path = _CI_DIR / "render_perf_dashboard.html"
    template = path.read_bytes().decode("utf-8")
    if template.count(_TEMPLATE_PLACEHOLDER) != 1:
        raise RuntimeError(f"{path} must contain {_TEMPLATE_PLACEHOLDER} exactly once")
    return template


_HTML_TEMPLATE = _load_html_template()


def render_html(bundle: dict[str, Any]) -> str:
    """Embed sanitized inline JSON into the self-contained HTML SPA."""
    inline = serialize_inline_json(bundle)
    return _HTML_TEMPLATE.replace(_TEMPLATE_PLACEHOLDER, inline, 1)


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
