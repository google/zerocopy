# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared imports, workflow paths, and `_make_record` for the performance
and docs workflow tests."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil

from anneal_ci_lib import WorkflowRepoFixture, find_workflow_step, load_workflow
import perf_tracking


CI_DIR = Path(__file__).resolve().parent.parent
ANNEAL_DIR = CI_DIR.parent
WORKFLOW_PATH = ANNEAL_DIR.parent / ".github/workflows/anneal-perf.yml"
DOCS_WORKFLOW_PATH = ANNEAL_DIR.parent / ".github/workflows/docs.yml"
BUDGETS_PATH = CI_DIR / "perf_budgets.json"


def _make_record(sha_idx: int, unix_ts: int, subject: str = "Test") -> dict:
    sha = f"{sha_idx:040x}"
    return {
        "schema": perf_tracking.RECORD_SCHEMA,
        "commit": {
            "sha": sha,
            "short_sha": sha[:12],
            "timestamp": "2026-11-23T06:00:00Z",
            "unix_ts": unix_ts,
            "subject": subject,
            "branch": "main",
        },
        "environment": {
            "profile": "github-ubuntu-24.04-x86_64",
            "os": "Linux",
            "arch": "x86_64",
            "cpu_model": "AMD EPYC 7763 64-Core Processor",
            "vcpu_count": 4,
            "ram_total_kib": 16374212,
            "lean_version": "4.34.1",
            "rustc_version": "rustc 1.98.0-nightly",
        },
        "sampling": {
            "verify_repeats": 3,
            "aggregation": "median",
            "rss_method": "usr_bin_time",
        },
        "metrics": {
            "verify.scalar.cold_prebuilt_total_ms": 10000.0 + sha_idx,
            "memory_rss.verify_scalar.cold_prebuilt_maxrss_kib": 500000,
            "artifact_size.bundled_olean.total_bytes": 12000000,
            "zerocopy_proofs.suite.verified_units_count": 5,
        },
    }
