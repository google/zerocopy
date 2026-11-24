# Anneal Performance Tracking, Regression Detection, and Static Dashboard Architecture

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Continuous verification performance tracking for Anneal must capture noisy sampled timings (`cargo-anneal verify`, cold `lean -j1` elaboration, `zerocopy/proofs/` end-to-end latency) alongside zero-variance (`CV = 0%`) structural metrics (3-part `.olean`/`.olean.server`/`.olean.private` byte sizes, Rust binaries, and verified unit counts) without expanding `anneal/trusted/` (`0` LOC delta) or weakening PR fork security.

This architecture specifies five components living entirely under `anneal/ci/` and `.github/workflows/anneal-perf.yml`:
1. **Fork-Safe Privilege Separation & Co-Tenancy on `benchmark-data`:** Untrusted `pull_request` jobs run strictly read-only (`contents: read`) against deterministic byte-size and catastrophic OOM/timeout budgets; only trusted `push: main` / `schedule` / `workflow_dispatch` runs persist telemetry to `anneal/records.jsonl` and render the zero-CDN dashboard under `dashboard/anneal/{index.html,data.json}` (served automatically at `https://google.github.io/zerocopy/bench/anneal/` by `.github/workflows/docs.yml` without clobbering root `zerocopy` Criterion benchmarks at `dashboard/`).
2. **Linux `exec_mm_put_old` `ru_maxrss` Isolation:** Spawning subprocesses from Python via `posix_spawn` (`CLONE_VM | CLONE_VFORK`) contaminates child `wait4` `ru_maxrss` with the Python parent's high-water RSS (`142,360 KiB` reported for `816 KiB` `/bin/true`). Launching timed commands through a fresh-`exec` `/usr/bin/time` wrapper (`< 2 MiB` binary) restores accurate grandchild peak RSS down to `20 MiB` checkers.
3. **Canonical JSONL (`anneal-perf-record/v1`) & Columnar Dashboard (`anneal-perf-dashboard/v1`):** Columnar series arrays shrink `2,000` commits $\times$ `60` metrics from `16.71 MiB` raw / `613.9 KiB` gzipped (`github-action-benchmark` `data.js`) to `1.05 MiB` raw / `27.8 KiB` gzipped (`22.09x` gzip reduction), while escaping `<`, `>`, `&`, `U+2028`, and `U+2029` inside inline `<script type="application/json">` data.
4. **Two-Tier Regression Engine:** Combines hard single-run caps (`perf_budgets.json`) with rolling `Median / MAD` ($W = 25$, `50%` breakdown point) z-score step detection (`confirmed_regression` when $(z_t > 3.5 \land z_{t-1} > 3.5 \land \Delta_t > 0.08)$ or $(z_t > 6.0 \land \Delta_t > 0.20 \land \neg\text{hw\_changed})$), CPU-SKU shift markers, and inversion-symmetric geometric-mean category summaries.

## Applicability

Findings apply to `google/zerocopy` at `a68641199cdfa99f96cb62f0cde921c9d36bfb22` (`anneal` `0.2.0-alpha.8`), `refs/heads/benchmark-data@d07175ed40ac6605442525427efbd86c76f8b199`, `.github/workflows/docs.yml:202-221`, Linux kernel `fs/exec.c:918`, and `zizmor v1.23.1 --persona pedantic` + `action-validator v0.8.0`.

## Findings

### 1. Fork-Safe Workflow Topology and `benchmark-data` Co-Tenancy

Basis: source + execution (`docs.yml:202-221`, `benchmark-data@d07175ed40`, `zizmor v1.23.1 --persona pedantic --offline` `0` findings).

- **Workflow (`.github/workflows/anneal-perf.yml`):** Workflow-level `permissions: {}`; single job `collect-and-publish` gated by `if: github.repository == 'google/zerocopy'` with job-scoped `permissions: { contents: write }` and `concurrency: { group: anneal-perf-tracking, cancel-in-progress: false }`. Triggers strictly on `push: { branches: [main] }`, daily `schedule: [{ cron: '17 04 * * *' }]`, and `workflow_dispatch` (never `pull_request` or `pull_request_target`).
- **Co-Tenancy:** `docs.yml` copies `../temp-bench/dashboard/*` from `benchmark-data` into `target/doc/bench/`. Placing Anneal's append-only log at `anneal/records.jsonl` (outside `dashboard/`, excluded from Pages uploads) and its static bundle at `dashboard/anneal/{index.html,data.json}` publishes to `/bench/anneal/` with `0` edits to `docs.yml` and `0` interference with `dashboard/{index.html,data.js}`.
- **Persistence:** Uses SHA-pinned `actions/checkout` (`persist-credentials: false`), verifies `trusted/root-manifest.sha256`, and commits to `benchmark-data` via an isolated temporary Git worktree with a 5-attempt `git fetch` + `(commit.sha, environment.profile)` idempotent replay + `git push` CAS loop.

### 2. Schemas (`anneal-perf-record/v1`, `anneal-perf-dashboard/v1`) and Five-Category Metric Suite

Basis: source + execution (`verify.rs`, `prebuild_bundled_oleans.py`, `verify_zerocopy.py`).

- **Metric Key Grammar:** `<category>.<subject>.<measure>` (`^[a-z0-9_]+(\.[a-z0-9_-]+){2,}$`), `category ∈ {"verify", "theory_elab", "memory_rss", "artifact_size", "zerocopy_proofs"}`, `unit ∈ {"ms", "KiB", "B", "count"}`, `direction ∈ {"lower_is_better", "higher_is_better", "informational"}`, `deterministic: bool`.
- **Five Metric Categories (`anneal/ci/perf_tracking.py`):**
  1. `verify`: `verify.scalar.{cold_no_cache,cold_prebuilt,warm_disk}_{total,capture,proof_audit}_ms` (`--no-cache`, fresh `$XDG_CACHE_HOME` + `--no-rebuild-bundled`, warm disk cache with prebuilt dir masked; median of `--repeats = 3`).
  2. `theory_elab`: `theory_elab.<mod_slug>.cold_j1_ms` and `summary.{critical_path_ms,total_cpu_ms,slowest_module_ms}` over topological `Trusted.*` (`19` modules), `Anneal.*` (`theory/bundle-manifest.json`), and `TrustedBoundary.lean` (`lean -j1 -t0 -DElab.async=false -Ddebug.skipKernelTC=false`, `-DwarningAsError=true` on `Anneal.*`).
  3. `memory_rss`: `memory_rss.<target>.maxrss_kib` via `/usr/bin/time -f "__ANNEAL_TIME_MAXRSS_KIB__=%M" -o <tmp> -- <cmd...>` (`fallback_wait4` via `fork+exec` only when `/usr/bin/time` is absent).
  4. `artifact_size`: Exact `st_size` of `.olean`/`.olean.server`/`.olean.private`, stripped Rust binaries (`cargo_anneal`, `anneal_rustc_capture`, `anneal_audit`), and `.tar.zst` archives (`CV = 0%`).
  5. `zerocopy_proofs`: `zerocopy_proofs.<unit>.{total,capture,proof_audit}_ms` and `zerocopy_proofs.suite.{total_ms,verified_units_count}` across `zerocopy/proofs/01..04`.
- **Linux `ru_maxrss` Isolation (`torvalds/linux` `fs/exec.c:918`):** Because `exec_mm_put_old` folds `old_mm` high-water RSS into the child's `signal->maxrss` under `posix_spawn` (`CLONE_VM | CLONE_VFORK`), wrapping spawns in `< 2 MiB` `/usr/bin/time` eliminated `142,360 KiB` vs. `816 KiB` contamination on `/bin/true`.

### 3. Two-Tier Regression Detection & Zero-CDN Static Dashboard

Basis: execution (Monte Carlo FPR/TPR `Probe 2`, `verify_ci_perf_tracking.py`).

- **Tier A (`perf_budgets.json`):** Hard `max_value` caps (public `.olean <= 3,145,728 B`, `TrustedBoundary.olean <= 25,165,824 B`, `.olean.private <= 12,582,912 B`, bundled `.olean* <= 67,108,864 B`, stripped `cargo-anneal <= 33,554,432 B`, cold `lean -j1 <= 75,000 ms`, `maxrss_kib <= 2,621,440 KiB`) and monotone floor (`zerocopy_proofs.suite.verified_units_count >= 4`).
- **Tier B (`Median / MAD` + Symmetric `GeoMean`):**
  - *Deterministic metrics:* Single-commit growth $\Delta_{\text{rel}} > +5.0\%$ and $\ge 4,096\text{ B}$ flags `"deterministic_growth"`.
  - *Sampled metrics:* Window $W_t$ ($W = 25$, min `5`), median $m_t$, $\hat{\sigma}_t = \max(1.4826 \cdot \text{MAD}(W_t), 0.015 \cdot m_t)$, $z_t = (x_t - m_t)/\hat{\sigma}_t$. Classifies `confirmed_regression` ($(z_t > 3.5 \land z_{t-1} > 3.5 \land \Delta_t > 0.08)$ or $(z_t > 6.0 \land \Delta_t > 0.20 \land \neg\text{hw\_changed})$), `candidate_spike` ($z_t > 4.0 \land \Delta_t > 0.10$), and `hardware_shift` (`cpu_model` change).
  - *Category summaries:* Unfiltered $\text{GeoMean}(B / A) = \exp(\frac{1}{|M|}\sum \ln(B_i / A_i))$, preserving $\text{GeoMean}(A / B) = \text{GeoMean}(B / A)^{-1}$.
- **Static Dashboard (`render_perf_dashboard.py`):** Pure Python 3.10+ stdlib generating `~20 KiB` inline SVG/Canvas UI with HTML5 `</script>` breakout neutralization (`\u003c`, `\u003e`, `\u0026`, `\u2028`, `\u2029`), sparkline grid, `Median ± 2σ_MAD` detail chart, sibling overlays, and `max-commits = 1,000` windowing.

### 4. Eliminated Alternatives (`E1`–`E7`) and Tunable Policy Defaults

Basis: source + execution (`support/anneal_perf_tracking_architecture.md` Partition 2 & Partition 3).

- **Eliminated alternatives:** `E1` running `auto-push: true` on `pull_request` / `pull_request_target` (`zizmor` `dangerous-triggers`); `E2` `benchmark-action/github-action-benchmark` (`22.09x` larger gzipped `data.js`, unpinned CDN `Chart.js`, `3.07–21.74` false alerts/100 commits via `cur / prev`); `E3` `Bencher`/`CodSpeed` (proprietary SaaS + `15x–359x` Valgrind slowdown); `E4` writing to root `dashboard/` (clobbers `docs.yml`); `E5` `Vega-Lite` (`1.1 MiB`) / `Chart.js` (`205 KiB`) CDN; `E6` Python `posix_spawn` `wait4` `ru_maxrss`; `E7` `Mean + 3.5 SD` (`8.4%` recall under `+40%` spike) and arithmetic mean of `%` changes (`+25.0%` bias on `[2.0x, 0.5x]`).
- **Tunable defaults (§8):** Daily `17 04 * * *` cron + `push: main`; `--repeats 3` for fast `verify.scalar` and `1` for cold/per-module/`zerocopy_proofs` (`< 25 min` on 4-core runners); non-blocking `$GITHUB_STEP_SUMMARY` regression alerts + blocking `--check-budgets`; `--max-commits 1000` inline dashboard window.

## Boundaries

- **not examined (post-30-commit `benchmark-data` baseline tightening):** Initial ceilings in `perf_budgets.json` are calibrated with wide runner headroom from `0.2.0-alpha.8` measurements and require tightening after accumulating `>= 30` `main` commits on `benchmark-data`.
- **known not to apply (`posix_spawn` `wait4` `ru_maxrss` on Linux):** Direct Python child `ru_maxrss` collection without fresh `exec` (`/usr/bin/time`) is falsified on Linux `fs/exec.c:918`.

## Evidence

- **Primary preserved architectural specification:** [anneal_perf_tracking_architecture.md](support/anneal_perf_tracking_architecture.md) (complete 3-partition specification, JSON schemas, metric table, two-tier formulas, and `E1`–`E7` trade-off analysis).
- **Primary sources & probes verified:** `google/zerocopy@a68641199cdfa99f96cb62f0cde921c9d36bfb22`, `refs/heads/benchmark-data@d07175ed40ac6605442525427efbd86c76f8b199`, `zizmor v1.23.1 --persona pedantic --offline` (`0` findings), `torvalds/linux` `fs/exec.c:918` `/usr/bin/time` isolation (`816 KiB` vs. `142,360 KiB`), and `verify_ci_perf_tracking.py` (`22.09x` wire compression + Monte Carlo FPR/TPR).

## Revalidation

1. Run `zizmor --persona pedantic` and `action-validator` on `.github/workflows/anneal-perf.yml` after any workflow edit.
2. Run `perf_tracking.py validate`, `perf_tracking.py check-budgets`, and `perf_tracking.py analyze` over `anneal/records.jsonl`, confirming `dashboard/anneal/{index.html,data.json}` renders without touching root `dashboard/{index.html,data.js}`.
3. On Linux runners, verify `/usr/bin/time` is present so `rss_method` does not degrade to `fallback_wait4`.
