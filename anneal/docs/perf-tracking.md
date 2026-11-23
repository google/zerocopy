<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal Performance Tracking and Benchmark Dashboard Architecture

> **Scope in This Tree:** This document specifies Anneal's continuous
> performance tracking, budget enforcement, static dashboard, and fork-safe CI
> architecture. This tree implements the complete pipeline across
> `anneal/ci/perf_tracking.py`, `anneal/ci/perf_budgets.json`,
> `anneal/ci/render_perf_dashboard.py`, `.github/workflows/anneal-perf.yml`,
> and their unit test suites.

## 1. Purpose, Scope, Guarantees, and Non-Goals

Anneal's verification pipeline spans Rust MIR extraction
(`anneal-rustc-capture`), staged Lean 4 elaboration and prebuilt `.olean`
caching (`cargo-anneal`), trust-boundary and proof-kernel auditing
(`anneal-audit`, `TrustedBoundary.lean`, `SpecPreflight.lean`, and external
NDJSON proof checkers), bundled proof libraries (`anneal/theory/`), and
verbatim production crate proofs (`zerocopy/proofs/`). Performance regressions
in this stack manifest across multiple resource dimensions: end-to-end CLI
latency, cold single-threaded `lean -j1` elaboration cliffs, subprocess peak
resident memory (`ru_maxrss`) approaching CI runner OOM limits, `.olean` /
`.olean.private` proof-term bloat, and packaged toolchain archive growth.

This architecture defines Anneal's continuous performance tracking, budget
enforcement, and interactive static dashboard pipeline.

### 1.1 Architectural Guarantees

1. **Fork-Safe Privilege Separation:** Pull-request checks execute strictly
   with read-only repository permissions (`contents: read`) and zero secret or
   deployment tokens. Only trusted runs on `google/zerocopy` (`push` to `main`,
   scheduled cron runs, and authorized `workflow_dispatch` runs) hold
   job-scoped `contents: write` permission to append telemetry to the orphan
   `benchmark-data` branch.
2. **Zero-TCB and Magnet-File Isolation:** All benchmark collection, schema
   validation, regression evaluation, and dashboard generation live outside
   `anneal/trusted/` under `anneal/ci/`, introducing zero production Cargo
   dependencies and zero trust-boundary surface expansion.
3. **Dual Wall-Clock and Zero-Variance Structural Telemetry:** Every collection
   run pairs noisy wall-clock measurements (`ms`) with zero-variance (`CV = 0%`)
   structural proxies—3-part `.olean` / `.olean.server` / `.olean.private` byte
   sizes, compiled Rust binary and prebuilt bundle sizes, and audited proof/unit
   cardinalities—so algorithmic proof-term blowups are caught deterministically
   regardless of shared-runner jitter.
4. **Uncontaminated Subprocess Memory Accounting:** On Linux, per-child peak
   resident set size (`ru_maxrss` in `KiB`) is measured through a lightweight
   fresh-`exec` wrapper (`/usr/bin/time`) rather than direct `posix_spawn`
   (`CLONE_VM`) parent `wait4` calls, preventing the collector's own historical
   `mm_struct` high-water RSS from contaminating small child measurements via
   `exec_mm_put_old`.
5. **Zero-SaaS, Zero-CDN Self-Contained Dashboard:** Historical records reside
   as canonical append-only JSON Lines (`anneal/records.jsonl`) on
   `benchmark-data` alongside a generated, zero-CDN static HTML/JS/CSS bundle
   under `dashboard/anneal/` (published automatically to
   `https://google.github.io/zerocopy/bench/anneal/` by
   `.github/workflows/docs.yml` without clobbering sibling `zerocopy` Criterion
   benchmarks at `dashboard/`).

### 1.2 Explicit Non-Goals

- **No Merge-Blocking PR Gates on Noisy Wall-Clock Micro-Shifts:** Shared cloud
  CI VMs exhibit `3%–12%` run-to-run wall-clock variance and occasional
  noisy-neighbor spikes. Pull-request gates enforce only deterministic byte-size
  budgets and generous catastrophic timeout/OOM ceilings; sensitive
  step-regression detection runs over continuous `main` history.
- **No External SaaS Telemetry or Runtime Third-Party CDNs:** Neither benchmark
  storage nor browser rendering depends on external SaaS APIs, hosted databases,
  or third-party JavaScript/font CDNs.
- **No In-Process Rust Microbenchmark Replacement:** Sub-microsecond Rust
  library microbenchmarks for `zerocopy` remain the domain of `Criterion`;
  Anneal's tracker measures multi-process verification, elaboration, memory, and
  artifact-footprint behavior.

---

## 2. System Topology and Trust Boundaries

```text
  Untrusted PRs (pull_request / merge_group)       Trusted Default Branch (push: main / schedule)
  ┌────────────────────────────────────────┐       ┌────────────────────────────────────────────┐
  │ permissions: { contents: read }        │       │ .github/workflows/anneal-perf.yml          │
  │ - Deterministic .olean* & binary caps  │       │ permissions: {} (root)                     │
  │ - Per-child ru_maxrss OOM ceilings     │       │ job permissions: { contents: write }       │
  │ - Zero writes to benchmark-data        │       │ concurrency: anneal-perf-tracking          │
  └────────────────────────────────────────┘       └─────────────────────┬──────────────────────┘
                                                                         │
                                                     1. Collect & validate (`perf_tracking.py`)
                                                     2. Append + CAS push & render bundle
                                                     3. Check Tier A budgets (fail on breach)
                                                                         │
                                                                         ▼
                                                   ┌────────────────────────────────────────────┐
                                                   │ Orphan Branch: refs/heads/benchmark-data   │
                                                   │ ├── dashboard/{index.html,data.js} (kept)  │
                                                   │ ├── anneal/records.jsonl   (canonical log) │
                                                   │ └── dashboard/anneal/                      │
                                                   │     ├── index.html (zero-CDN SPA + inline) │
                                                   │     └── data.json  (columnar series + reg) │
                                                   └─────────────────────┬──────────────────────┘
                                                                         │
                                                     Checked out read-only (`persist-credentials: false`)
                                                     by `.github/workflows/docs.yml` (`temp-bench`)
                                                                         │
                                                                         ▼
                                                   ┌────────────────────────────────────────────┐
                                                   │ GitHub Pages (`actions/deploy-pages`)      │
                                                   │ https://google.github.io/zerocopy/         │
                                                   │   └── bench/anneal/{index.html,data.json}  │
                                                   └────────────────────────────────────────────┘
```

### 2.1 Co-Tenancy on `refs/heads/benchmark-data`

`.github/workflows/docs.yml` checks out `ref: benchmark-data` into `temp-bench`
and copies `../temp-bench/dashboard/*` into `target/doc/bench/` prior to
`actions/upload-pages-artifact`. Because `benchmark-data` already hosts
`dashboard/index.html` and `dashboard/data.js` at the `dashboard/` root, Anneal
namespaces all persisted artifacts strictly under two disjoint paths:

- `anneal/records.jsonl`: canonical append-only per-commit telemetry log
  (outside `dashboard/`, so raw historical logs do not bloat the deployed Pages
  artifact);
- `dashboard/anneal/{index.html,data.json}`: self-contained static dashboard
  mounted at `/bench/anneal/` on GitHub Pages. `.github/workflows/docs.yml`
  copies `dashboard/*` into `target/doc/bench/` and triggers on
  `workflow_run` completions of `Build & Tests`, `Anneal Tests`, and
  `Anneal Performance Tracking` (`main`).

---

## 3. Canonical Telemetry and Dashboard Schemas

### 3.1 Uniform Metric Naming and Descriptor Model

Every scalar measurement is identified by a dot-separated ASCII key
`<category>.<subject>.<measure>` and governed by a static `MetricDescriptor`:

| Field | Type | Allowed Values & Semantics |
| :--- | :--- | :--- |
| `id` | `str` | Canonical dot-separated identifier matching `^[a-z0-9_]+(\.[a-z0-9_-]+){2,}$`. |
| `label` | `str` | Human-readable metric title displayed in charts and tables. |
| `category` | `str` | One of `"verify"`, `"theory_elab"`, `"memory_rss"`, `"artifact_size"`, `"zerocopy_proofs"`. |
| `group` | `str` | Logical comparison group (for example, `"verify.scalar.total"` groups cold, prebuilt, and warm `scalar` verification times for single-click multi-series overlay). |
| `unit` | `str` | One of `"ms"`, `"KiB"`, `"B"`, `"count"`. |
| `direction` | `str` | `"lower_is_better"` (latencies, RSS, byte sizes), `"higher_is_better"` (verified item counts), or `"informational"`. |
| `deterministic` | `bool` | `true` for zero-variance structural metrics (`.olean*` bytes, binary sizes, counts); `false` for wall-clock timings and sampled RSS. |

### 3.2 Append-Only Per-Commit Record (`anneal-perf-record/v1`)

Each line of `anneal/records.jsonl` is a canonical, UTF-8, key-sorted
single-line JSON object:

```json
{
  "schema": "anneal-perf-record/v1",
  "commit": {
    "sha": "a68641199cdfa99f96cb62f0cde921c9d36bfb22",
    "short_sha": "a68641199cdf",
    "timestamp": "2026-11-23T06:45:43Z",
    "unix_ts": 1795416343,
    "subject": "Release Anneal 0.2.0-alpha.8",
    "branch": "main"
  },
  "environment": {
    "profile": "github-ubuntu-24.04-x86_64",
    "os": "Linux",
    "arch": "x86_64",
    "cpu_model": "AMD EPYC 7763 64-Core Processor",
    "vcpu_count": 4,
    "ram_total_kib": 16374212,
    "lean_version": "4.34.1",
    "rustc_version": "rustc 1.98.0-nightly (2026-05-31)"
  },
  "sampling": {
    "verify_repeats": 3,
    "aggregation": "median"
  },
  "metrics": {
    "verify.scalar.cold_no_cache_total_ms": 50070.0,
    "verify.scalar.cold_no_cache_capture_ms": 1316.0,
    "verify.scalar.cold_no_cache_proof_audit_ms": 48742.0,
    "verify.scalar.cold_prebuilt_total_ms": 10274.0,
    "verify.scalar.warm_disk_total_ms": 9217.0,
    "memory_rss.verify_scalar.cold_no_cache_maxrss_kib": 948120,
    "theory_elab.anneal_mirwp_execution.cold_j1_ms": 8850.0,
    "memory_rss.theory_anneal_mirwp_execution.cold_j1_maxrss_kib": 512400,
    "artifact_size.bundled_olean.public_bytes": 11842560,
    "artifact_size.bundled_olean.private_bytes": 24812032,
    "artifact_size.bundled_olean.total_bytes": 37870350,
    "artifact_size.bin.cargo_anneal_bytes": 8912448,
    "zerocopy_proofs.01_usize_pointer_metadata.warm_total_ms": 11420.0,
    "zerocopy_proofs.suite.verified_units_count": 4
  }
}
```

**Schema Invariants:**

1. Unknown top-level keys or unsupported `"schema"` strings are rejected
   fail-closed by `perf_tracking.py validate`.
2. Numeric metric values must be finite (`!math.isnan(v) and !math.isinf(v)`)
   and non-negative (`v >= 0`), excluding booleans.
3. Records in `anneal/records.jsonl` are deduplicated by
   `(commit.sha, environment.profile)` in chronological order: rerunning the
   collector on an already-recorded `(sha, profile)` replaces that entry
   idempotently rather than appending a duplicate commit point.

### 3.3 Columnar Dashboard Bundle (`anneal-perf-dashboard/v1`)

To minimize HTTP transfer size and browser parse latency (`27.8 KiB` gzipped
across `2,000` commits and `60` metrics vs. `613.9 KiB` gzipped for
denormalized `github-action-benchmark` `data.js`), `render_perf_dashboard.py`
compiles `anneal/records.jsonl` into a dense columnar structure:

```json
{
  "schema": "anneal-perf-dashboard/v1",
  "repo_url": "https://github.com/google/zerocopy",
  "generated_at": "2026-11-23T07:00:00Z",
  "profile": "github-ubuntu-24.04-x86_64",
  "commits": [
    {
      "sha": "a68641199cdfa99f96cb62f0cde921c9d36bfb22",
      "short": "a68641199cdf",
      "ts": 1795416343,
      "subject": "Release Anneal 0.2.0-alpha.8",
      "cpu_model": "AMD EPYC 7763 64-Core Processor",
      "hw_changed": false
    }
  ],
  "metrics": {
    "verify.scalar.cold_prebuilt_total_ms": {
      "label": "scalar verify (cold prebuilt .olean)",
      "category": "verify",
      "group": "verify.scalar.total",
      "unit": "ms",
      "direction": "lower_is_better",
      "deterministic": false,
      "budget_max": 25000.0
    }
  },
  "series": {
    "verify.scalar.cold_prebuilt_total_ms": [10274.0]
  },
  "summaries": {
    "category_geomean_vs_prev": {
      "verify": 1.0,
      "theory_elab": 1.0,
      "memory_rss": 1.0,
      "artifact_size": 1.0,
      "zerocopy_proofs": 1.0
    }
  },
  "anomalies": []
}
```

**Alignment Invariant:** Every array `series[metric_id]` has exact length
`len(commits)`, using `null` at index `i` whenever commit `i` did not record
`metric_id`.

---

## 4. Initial Metric Suite and Subprocess Measurement Protocol

### 4.1 Five-Category Initial Metric Catalog

| Category | Metric ID Pattern | Source & Collection Method | Variance Class |
| :--- | :--- | :--- | :--- |
| **`verify` (CLI End-to-End & Phases)** | `verify.scalar.{cold_no_cache,cold_prebuilt,warm_disk}_{total,capture,proof_audit}_ms` | Runs `cargo-anneal verify` on `trusted/cargo-anneal/tests/fixtures/scalar`: (1) `--no-cache`, (2) fresh empty `$XDG_CACHE_HOME` with prebuilt archive (`--no-rebuild-bundled`, when `share/anneal/prebuilt/manifest.json` exists), and (3) warm `$XDG_CACHE_HOME` (`--no-rebuild-bundled` without `share/anneal/prebuilt`), extracting Receipt v3 `timing_ms.{total,capture,proof_and_audit}` across $k$ repeats (median). | Sampled (`CV ~3–8%`) |
| **`theory_elab` (Cold Per-Module `lean -j1`)** | `theory_elab.<mod_slug>.cold_j1_ms` & `theory_elab.summary.{critical_path_ms,total_cpu_ms,slowest_module_ms}` | Compiles bundled `Trusted.*`, `Anneal.*` (`theory/bundle-manifest.json`), and `TrustedBoundary.lean` in topological order under `lean -j1 -t0 -DElab.async=false -Ddebug.skipKernelTC=false` (plus `-DwarningAsError=true` for `Anneal.*`). | Sampled (`CV ~2–6%`) |
| **`memory_rss` (Isolated Peak RSS)** | `memory_rss.<target>.maxrss_kib` | Captures per-child peak RSS (`KiB`) via fresh-`exec` `/usr/bin/time` wrapper across `cargo-anneal verify`, `TrustedBoundary.lean`, and every cold `lean -j1` module compile, plus `memory_rss.theory_elab.max_module_maxrss_kib`. | Low-noise (`CV < 2%`) |
| **`artifact_size` (Deterministic Footprints)** | `artifact_size.bundled_olean.{public,private,server,total}_bytes`, `artifact_size.module.<mod_slug>.{olean,olean_server,olean_private}_bytes`, `artifact_size.bin.{cargo_anneal,anneal_rustc_capture,anneal_audit}_bytes`, `artifact_size.archive.omnibus_tar_zst_bytes` | Exact `st_size` byte counts of compiled `.olean` / `.olean.server` / `.olean.private` artifacts, release Rust binaries, and (when built) the packaged `.tar.zst` toolchain archive. | Deterministic (`CV = 0%`) |
| **`zerocopy_proofs` (First-Customer Suite)** | `zerocopy_proofs.<unit>.{total,capture,proof_audit}_ms`, `zerocopy_proofs.suite.{total_ms,verified_units_count}` | Invokes `cargo-anneal verify` across `zerocopy/proofs/*` with warm/prebuilt `.olean` cache against unmodified `zerocopy/src/`. | Sampled (`ms`) + Deterministic (`count`) |

### 4.2 Linux `exec_mm_put_old` `ru_maxrss` Isolation Rule

In the Linux kernel (`fs/exec.c:exec_mm_put_old`), `execve` calls
`setmax_mm_hiwater_rss(&current->signal->maxrss, old_mm)`, folding the
pre-`exec` address space's high-water RSS into the child's `signal->maxrss`.
When Python's `subprocess.Popen` spawns a child on Linux via `posix_spawn`
(`CLONE_VM | CLONE_VFORK`), `old_mm` is the Python parent's `mm_struct`,
contaminating every child's `wait4` `ru_maxrss` with the parent's all-time peak
RSS even after `munmap`.

`anneal/ci/perf_tracking.py` eliminates this contamination by launching timed
subprocesses on Linux through
`/usr/bin/time -f "__ANNEAL_TIME_MAXRSS_KIB__=%M" -o <tmpfile> -- <cmd...>`
(falling back to isolated `fork+exec` + `wait4` only when `/usr/bin/time` is
absent and recording `"rss_method": "fallback_wait4"`). Because `/usr/bin/time`
`execve`s into a `< 2 MiB` C binary before `fork + exec + wait4`ing `<cmd...>`,
the measured grandchild's `old_mm` carries `< 2 MiB` high-water RSS, preserving
accurate memory telemetry down to small verifier tools.

---

## 5. Two-Tier Regression Detection, Aggregation, and Budgets

### 5.1 Tier A — Deterministic and Catastrophic Budget Gate

`perf_tracking.py check-budgets` evaluates a single run record against
`anneal/ci/perf_budgets.json` (suitable for both `pull_request` validation and
`main` runs):

- **Hard Upper Ceilings (`max_value`):**
  - Deterministic artifact caps (`Trusted` / `Trusted.*` / `Anneal.*` public
    `.olean <= 3,145,728 B`, `TrustedBoundary.olean <= 25,165,824 B`, per-module
    `.olean.private <= 12,582,912 B`, bundled `.olean*` sum `<= 67,108,864 B`,
    compiled `cargo-anneal` / `anneal-rustc-capture` / `anneal-audit` binaries
    `<= 33,554,432 B` each).
  - Catastrophic memory and timeout caps calibrated with wide runner headroom
    (per-module `lean -j1` `maxrss_kib <= 2,621,440 KiB` [`2.5 GiB`], per-module
    cold `lean -j1 <= 75,000 ms` below `installed_smoke`'s `120 s` child
    timeout).
- **Monotone Ratchet Floors (`min_value`):**
  - `zerocopy_proofs.suite.verified_units_count >= 4` (non-backsliding
    first-customer coverage).

### 5.2 Tier B — Rolling `Median / MAD` Continuous Time-Series Detector

Over historical `anneal/records.jsonl` commits matching the same
`environment.profile`, `perf_tracking.py analyze` evaluates each
`lower_is_better` metric $x_t$ against its trailing baseline window
$W_t = (x_{t-W}, \dots, x_{t-1})$ (default $W = 25$ non-null commits, minimum
`5` commits):

1. **Deterministic Metrics (`deterministic == true`):**
   - Baseline noise is zero. Any single-commit jump
     $\Delta_{\text{rel}} = (x_t - x_{t-1}) / \max(x_{t-1}, 1) > \tau_{\text{det}}$
     (default `+5.0%` and `>= 4,096 B` for byte metrics) emits a
     `"deterministic_growth"` notice; breaching `budget_max` emits a
     `"budget_breach"` error.
2. **Sampled Wall-Clock and RSS Metrics (`deterministic == false`):**
   - Compute rolling median $m_t = \text{median}(W_t)$ and scaled Median
     Absolute Deviation:
     $$\hat{\sigma}_t = \max\!\Bigl(1.4826 \cdot \text{median}_{y \in W_t}\lvert y - m_t\rvert,\; 0.015 \cdot m_t\Bigr)$$
   - Compute robust z-score $z_t = (x_t - m_t) / \hat{\sigma}_t$ and relative
     delta $\Delta_t = (x_t - m_t) / m_t$.
   - Classify commit $t$:
     - **`confirmed_regression` (High confidence):**
       $(z_t > 3.5 \land z_{t-1} > 3.5 \land \Delta_t > 0.08)$ (sustained
       2-commit step shift) **or** $(z_t > 6.0 \land \Delta_t > 0.20)$ when
       `hw_changed == false`.
     - **`candidate_spike` (Informational):** $z_t > 4.0 \land \Delta_t > 0.10$
       on a single commit (annotated on the dashboard, awaiting next-commit
       confirmation to suppress transient shared-runner spikes).
     - **`hardware_shift` (Contextual):**
       `commits[t].cpu_model != commits[t-1].cpu_model` (annotated with a
       vertical dashed marker on time-series charts so hypervisor CPU SKU
       changes are never misread as code regressions).
3. **Inversion-Symmetric Suite Summaries:**
   For any category or comparison commit pair $(A, B)$, multi-metric headline
   ratios use the **unfiltered geometric mean of ratios**:
   $$\text{GeoMean}(B / A) = \exp\!\left(\frac{1}{|M|}\sum_{i \in M} \ln\!\left(\frac{B_i}{A_i}\right)\right)$$
   preserving exact inversion symmetry
   $\text{GeoMean}(A / B) = \text{GeoMean}(B / A)^{-1}$.

---

## 6. Self-Contained Interactive Dashboard and Fork-Safe Workflow

### 6.1 Static Dashboard Architecture (`anneal/ci/render_perf_dashboard.py`)

`render_perf_dashboard.py` emits `dashboard/anneal/data.json` and
`dashboard/anneal/index.html` using pure Python 3.10+ standard-library code with
zero npm build steps and zero external runtime URLs:

1. **HTML5 `<script>` Breakout Neutralization:** When embedding `data.json`
   inside `<script id="anneal-perf-inline-data" type="application/json">`, all
   `<`, `>`, `&`, `U+2028`, and `U+2029` characters are escaped as `\u003c`,
   `\u003e`, `\u0026`, `\u2028`, and `\u2029`, neutralizing HTML5 script-tag
   breakouts from arbitrary commit messages while round-tripping identically
   through `JSON.parse`.
2. **Interactive Navigation and Drill-Down Views:**
   - **Header & KPI Summary Bar:** Latest commit link (`short_sha`), timestamp,
     runner hardware profile, active anomaly count badge, and 5 category
     geometric-mean delta cards (`Verify`, `Theory Cold Elab`, `Peak RSS`,
     `Artifact Sizes`, `Zerocopy Proofs`) against the rolling 25-commit
     baseline.
   - **Controls Toolbar:** Instant substring search, category filter pills,
     commit-window selector (`Last 50`, `Last 200`, `All`), baseline comparator
     selector (`Rolling 25-commit median`, `Previous commit`, or any pinned
     commit SHA), and `Download JSON` export button.
   - **Overview Sparkline Grid:** Compact responsive cards per metric showing
     current value, formatted unit, `%` delta vs. baseline,
     regression/deterministic badge, and inline SVG sparkline with budget
     ceiling line.
   - **Interactive Detail Chart Panel:** Clicking any sparkline card opens a
     high-DPI detail chart plotting the primary series, shaded rolling
     `Median ± 2σ_MAD` band, horizontal `budget_max` threshold line, automatic
     **Group Sibling Overlay** toggle, vertical markers for
     `confirmed_regression` and `hw_changed` transitions, hover crosshair
     tooltip, and click-through to `https://github.com/google/zerocopy/commit/<sha>`.

### 6.2 Fork-Safe GitHub Actions Workflow (`.github/workflows/anneal-perf.yml`)

`.github/workflows/anneal-perf.yml` satisfies `zizmor --persona pedantic` and
`action-validator`:

- **Triggers:**
  `on: { push: { branches: [main] }, schedule: [{ cron: '17 04 * * *' }],`
  `workflow_dispatch: {} }` — never `pull_request` or `pull_request_target`.
- **Permissions:** Workflow-level `permissions: {}`; single job
  `collect-and-publish` gated by `if: github.repository == 'google/zerocopy'`
  with documented `permissions: { contents: write }` scoped to appending
  telemetry to the orphan `benchmark-data` branch.
- **Concurrency:**
  `concurrency: { group: anneal-perf-tracking, cancel-in-progress: false }` so
  rapid `main` merges serialize cleanly without aborting in-progress
  measurements.
- **Root TCB Manifest, Checkout Hygiene, & Publish-Before-Gate Ordering:**
  `actions/checkout` is pinned by 40-hex commit SHA with
  `persist-credentials: false`, verifying `trusted/root-manifest.sha256` and
  symlink/override guards before building or invoking Anneal binaries. After
  `perf_tracking.py collect` and `perf_tracking.py validate` succeed,
  `Publish telemetry and dashboard` always runs first—using an isolated
  temporary clone authenticated strictly in that step via `GH_TOKEN` with a
  5-attempt `git fetch origin benchmark-data` + idempotent replay + `git push`
  compare-and-swap loop, plus a Markdown table and anomaly report written to
  `$GITHUB_STEP_SUMMARY`—so budget breaches remain visible in red on
  `dashboard/anneal/`. A final `Check performance budgets` step (with no
  `GH_TOKEN`) then runs `perf_tracking.py check-budgets` and fails CI if any
  Tier A budget is violated.
- **GitHub Pages Redeployment (`.github/workflows/docs.yml`):** `docs.yml`
  listens on `workflow_run` (`completed`, `branches: [main]`) for
  `Anneal Performance Tracking` in addition to `Build & Tests` and
  `Anneal Tests`. When triggered by `anneal-perf.yml`, `coordinate` verifies by
  workflow path/filename that the run belongs to `google/zerocopy` (`main`,
  `push`/`schedule`/`workflow_dispatch`) and that its
  `Publish telemetry and dashboard` step concluded `success` (even if the final
  `Check performance budgets` step failed), confirms both `ci.yml` and
  `anneal.yml` succeeded on `push` for the same commit, and verifies that
  commit still matches `refs/heads/main` before building rustdoc and copying
  `benchmark-data/dashboard/*` read-only (`persist-credentials: false`) to
  GitHub Pages.
