# Continuous Performance Tracking on Public GitHub Actions: Fork-Safe Storage, Static GitHub Pages Dashboards, Linux `ru_maxrss` Accounting, and Regression Detection

## Summary

1. **Fork-safe benchmark collection and GitHub Pages publication under `zizmor --persona pedantic` (`google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d`, `zizmorcore/zizmor@0b77258cf93d4e0ae762c843422c333faf2793f6`):** Combining `pull_request` or `pull_request_target` execution of untrusted fork code with `contents: write` or `pages: write` tokens enables orphan-branch history poisoning or privileged repository compromise (`zizmor` `dangerous-triggers` and `excessive-permissions`). Separating benchmark pipelines into (a) read-only `pull_request` / `merge_group` deterministic ceiling gates (`permissions: { contents: read }`), (b) a default-branch `push` / `schedule` / `workflow_dispatch` collector that appends canonical records to an orphan Git branch (`benchmark-data`) using bounded compare-and-swap (`git pull --rebase` / fast-forward retry) under `concurrency: { cancel-in-progress: false }`, and (c) an exact-SHA-revalidated GitHub Pages publisher (`actions/upload-pages-artifact` + `actions/deploy-pages` under `pages: write` and `id-token: write`) passes `zizmor v1.23.1 --persona pedantic` with zero findings while preserving zero-SaaS repository self-containment.
2. **Continuous-benchmarking platform trade-offs (`github-action-benchmark`, `Bencher`, `CodSpeed`, `rustc-perf`, vs. orphan-branch `JSONL` + columnar static bundle):**
   - `benchmark-action/github-action-benchmark@84ec6ea748925b6580796c05ce7a1c8fd0d15f3b` (`v1.22.2`) stores history in a monolithic indented `window.BENCHMARK_DATA` JavaScript file (`src/write.ts:21`) whose default `index.html` loads unpinned `Chart.js@2.9.2` from `https://cdn.jsdelivr.net` without Subresource Integrity (SRI) and evaluates alerts strictly against the single immediately preceding commit (`ratio > threshold`, `src/write.ts:98-120`). Across `2,000` commits $\times$ `60` metrics (`120,000` points), `window.BENCHMARK_DATA` reaches **`16.71 MiB` raw (`613.9 KiB` gzip)**—**`3.97x` raw / `10.66x` gzip larger** than normalized append-only `JSONL` (`4.21 MiB` raw / `57.6 KiB` gzip) and **`15.96x` raw / `22.09x` gzip larger** than a columnar dashboard JSON payload (`1.05 MiB` raw / `27.8 KiB` gzip).
   - `bencherdev/bencher@a39a1f4fb7d2a0bffcfc2d4d044852072ce98358` (`v0.6.17`) dual-licenses core crates (`MIT OR Apache-2.0`) while placing server/cloud modules (`plus/*`) under the proprietary `Bencher Plus License` (`LICENSE.md`), requiring either external SaaS API tokens (`bencher.dev`) or self-hosted server infrastructure.
   - `CodSpeedHQ/action@b1f28b5eccf7cb5bfe6a2a89cb3053eb67f1150c` (`v5.8.0`) achieves sub-`0.1%` CPU instruction variance via Valgrind/Cachegrind simulation, but relies on external SaaS ingestion and incurs `15x`–`359x` dynamic binary instrumentation overhead, making whole-toolchain Rust/Lean subprocess verification pipelines (`10`–`60 s` native wall time) impractical inside standard CI budgets.
3. **Self-contained interactive dashboard engines and HTML5 `<script>` injection safety (`leeoniya/uPlot@a8b48ee3a2ec53700194155fbfd8db71e0ca9fef`, `chartjs/Chart.js@ff1bdc38a102e7b9e97756041b1118272ed08564`, `vega/vega-lite@9d3a9a2e87ebbae0a525f1169b85b82fed986a21`):** Zero-dependency SVG/Canvas rendering (~`15`–`25 KiB` inline JS/CSS) or vendored `uPlot 1.6.32` (`80,073 B` `uPlot.iife.min.js` + `3,159 B` `uPlot.min.css`, MIT) eliminates third-party CDN runtime dependencies, offline breakage, and CSP/SRI drift, whereas `Chart.js v4.6.1` (~`205 KiB` minified) and `Vega-Lite v6.5.0` (`vega` + `vega-lite` + `vega-embed` > `1.1 MiB` minified) add substantial bundle weight. Any generator embedding commit metadata inside `<script type="application/json">` or inline JS **must** escape `<`, `>`, `&`, `U+2028`, and `U+2029` (`\u003c`, etc.) because HTML5 script-data tokenization closes `<script>` on literal `</script>` before JSON parsing occurs.
4. **Shared-runner regression detection and deterministic verification proxies:** On shared cloud CI runners exhibiting log-normal variance ($\sigma \in [0.03, 0.12]$) plus `3%` single-commit noisy-neighbor spikes (`+25%` to `+55%`), single-step adjacent ratio alerting (`github-action-benchmark` at `1.15x`) suffers **`3.07` to `21.74` false positives per `100` commits**, while parametric rolling mean + standard-deviation boundaries (`3.5 SD`) and rolling adjacent-delta IQR fences lose sensitivity (`TPR` dropping to `3.2%`–`8.4%` at $\sigma = 0.08$ on a `+15%` step) because outliers inflate baseline dispersion. Pairing **$k = 3$ in-job medians** with a **rolling $W = 25$ `Median / MAD` robust z-score** (`D4`: `0.34`–`0.58` FPR/100 commits, `98.0%` TPR at $\sigma = 0.03$) or **2-consecutive-commit step confirmation** (`D6`: `<= 0.02` FPR/100 commits, `98.4%` TPR at $\sigma = 0.03$), alongside **zero-variance deterministic proxies** (`.olean` / `.olean.private` / `.olean.server` byte sizes, archive/binary byte sizes, and exported proof declaration counts) and **symmetric suite geometric means** $\exp(\frac{1}{N}\sum \ln(B_i/A_i))$, separates true regressions from runner jitter.
5. **Linux `execve` `ru_maxrss` high-water mark contamination (`torvalds/linux@65e4fd942f72a9dba0e4e257290c4fa1aa756854`):** In `fs/exec.c:916-921` (`exec_mm_put_old`), Linux calls `setmax_mm_hiwater_rss(&current->signal->maxrss, old_mm)` during `execve`, folding the pre-`exec` address space's peak RSS into the child's `signal->maxrss` (`wait4` `ru_maxrss`). Spawning a small binary (`1 MiB` true RSS) from a `128 MiB` Python or Rust collector via `fork() + execve()` inflates reported child `ru_maxrss` to `~139 MiB` while `MAP_PRIVATE` pages are mapped, and spawning via `posix_spawn` / `vfork` (`CLONE_VM | CLONE_VFORK`, default in Python 3.8+ `subprocess.Popen`) inflates child `ru_maxrss` to `~142 MiB` **even after `munmap`** because `copy_mm` (`kernel/fork.c:1598`) shares the parent's `mm_struct` and its all-time `hiwater_rss`. Accurate per-process `ru_maxrss` requires spawning through a lightweight fresh-`exec` shim (such as `/usr/bin/time` or a minimal C/Rust launcher whose own peak RSS is `< 2 MiB`) so the measured grandchild's `old_mm` has negligible high-water RSS.

## Applicability

These findings apply to continuous performance tracking, artifact-size telemetry, regression gating, and static interactive dashboard publication for Rust and Lean 4 verification repositories hosted on public GitHub repositories using GitHub Actions and GitHub Pages.

- **Directly examined subjects and revisions:**
  - `google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d` (including historical workflow transitions at `962a5a3a82822f05b6201d475e737a1615f28f3e`, `d74fc66829d3cdc5d374c37de2ee46c22b2153b4`, and `ff55d9d48f95acca17275bea53dcb3145f5225a5`, plus the repository's orphan `benchmark-data` tree at `d07175ed40ac6605442525427efbd86c76f8b199`);
  - `benchmark-action/github-action-benchmark@84ec6ea748925b6580796c05ce7a1c8fd0d15f3b` (`v1.22.2`);
  - `bencherdev/bencher@a39a1f4fb7d2a0bffcfc2d4d044852072ce98358` (`v0.6.17`);
  - `CodSpeedHQ/action@b1f28b5eccf7cb5bfe6a2a89cb3053eb67f1150c` (`v5.8.0`) and `CodSpeedHQ/codspeed-rust@6ab62f6d0545adf2052e413e349c8b529904e575` (`v6.1.0`);
  - `rust-lang/rustc-perf@15d95905429e577d5a710b17c49e04b4451c263b`;
  - `zizmorcore/zizmor@0b77258cf93d4e0ae762c843422c333faf2793f6` (`v1.23.1`);
  - `leeoniya/uPlot@a8b48ee3a2ec53700194155fbfd8db71e0ca9fef` (`1.6.32`), `chartjs/Chart.js@ff1bdc38a102e7b9e97756041b1118272ed08564` (`v4.6.1`), and `vega/vega-lite@9d3a9a2e87ebbae0a525f1169b85b82fed986a21` (`v6.5.0`);
  - `torvalds/linux@65e4fd942f72a9dba0e4e257290c4fa1aa756854` (`kernel/fork.c` and `fs/exec.c`);
  - `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).
- **Subject relationships:** `google/zerocopy` provides the concrete multi-stage Rust MIR capture + Lean 4 elaboration/audit workload (`cargo-anneal`, `anneal-rustc-capture`, `anneal-audit`, `zerocopy/proofs/`), GitHub Pages deployment pipeline (`.github/workflows/docs.yml`), and `zizmor` security policy (`.github/workflows/ci.yml:1219-1239`). `github-action-benchmark`, `Bencher`, `CodSpeed`, and `rustc-perf` are evaluated as comparative continuous-benchmarking architectures; `uPlot`, `Chart.js`, and `Vega-Lite` are evaluated as browser visualization substrates; and `torvalds/linux` governs subprocess memory telemetry on Linux CI hosts.
- **Environment constraints:** Execution probes ran on `x86_64` Linux (`Python 3.13`, `zizmor 1.23.1`). Note that `ru_maxrss` units differ by OS (`KiB` on Linux vs. `bytes` on macOS/BSD `getrusage(2)`), and the `exec_mm_put_old` `CLONE_VM` `hiwater_rss` inheritance behavior is specific to the Linux kernel's `mm_struct` lifecycle.

## Findings

### 1. Continuous-Benchmarking Architecture Matrix for Public OSS GitHub Actions

`Basis: source + execution + derived`

Public open-source repositories running GitHub Actions face four simultaneous constraints that eliminate naive benchmark integrations:
1. **Untrusted fork PR execution:** `pull_request` runs untrusted code with a read-only `GITHUB_TOKEN` and no secrets; `pull_request_target` holds write permissions and secrets on the base repository and must never check out or execute PR head code.
2. **Static workflow analysis (`zizmor --persona pedantic`):** In `google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d` (`.github/workflows/ci.yml:1219-1239`), `zizmor` runs with `persona: pedantic` and `min-severity: medium` as a merge-blocking check. Execution of `zizmor v1.23.1 --persona pedantic --offline` confirms:
   - Workflow-level `contents: write` triggers `error[excessive-permissions]` (High);
   - `pull_request_target` triggers `error[dangerous-triggers]` (Medium);
   - Job-level write permissions without inline `# explanatory comment` trigger `help[undocumented-permissions]`;
   - Workflows lacking `concurrency:` trigger `help[concurrency-limits]`;
   - Unpinned tags (`@v1`) or `persist-credentials` omissions trigger `unpinned-uses` and `artipacked` findings.
3. **Multi-process macro-workloads:** Verifier pipelines spawn sandboxed `rustc`, `lean`, and external proof-kernel child processes taking `0.4`–`60 s` and `20`–`950 MiB` RSS, rather than nanosecond in-process Rust microbenchmarks (`#[bench]` / `Criterion`).
4. **Zero-SaaS durability and offline/CSP self-containment:** Historical performance series and dashboards must remain auditable, forkable, and viewable without proprietary SaaS tokens, external database hosting, or unpinned third-party CDNs.

| Architecture Option | Storage & Hosting | Fork-PR Security & `zizmor` Posture | Multi-Process & Multi-Metric Support | Variance Control & Regression Math | Licensing & Lock-In |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Orphan Git branch (`JSONL` + columnar `data.json`) + self-contained static HTML/JS on GitHub Pages** | Append-only `records.jsonl` + generated static `dashboard/` on orphan branch (e.g., `benchmark-data`), deployed via `docs.yml` (`actions/deploy-pages`) | **Clean (`0` `zizmor` findings):** PR jobs stay `contents: read` (enforcing deterministic/hard-ceiling gates only); only `push: [main]` / `schedule` jobs hold job-scoped `contents: write` | Native multi-dimensional records per commit (wall `ms`, phase `ms`, per-child `ru_maxrss`, `.olean*`/archive/binary bytes, decl counts) | Configurable in-repo Python/JS engine: $k$-sample medians, rolling `Median/MAD`, 2-commit step confirmation, geomean ratios, hard byte/RSS budgets | `100%` in-repo (`MIT OR Apache-2.0 OR BSD`); zero external SaaS or CDN |
| **`github-action-benchmark` (`v1.22.2`, `84ec6ea748...`)** | Single monolithic `window.BENCHMARK_DATA` (`data.js`) + `index.html` on `gh-pages` / `benchmark-data` | Requires `contents: write` in the benchmarking job (`962a5a3a82` granted `contents: write` to CI jobs; breaks fork PRs if `auto-push: true` runs on `pull_request`) | Flat `{name, unit, value, range?, extra?}` array (`customSmallerIsBetter`); splits suites into disconnected stacked charts | **Fragile on shared runners:** `findAlerts` (`src/write.ts:98-120`) compares strictly `cur / prev > threshold` (`1` prior commit!), causing `3`–`22%` FPR under runner jitter | `MIT`, but generated `index.html` hardcodes `<script src="https://cdn.jsdelivr.net/npm/chart.js@2.9.2/dist/Chart.min.js">` with zero SRI |
| **`Bencher` (`v0.6.17`, `a39a1f4fb7...`)** | Cloud API (`api.bencher.dev`) or self-hosted Rust + SQLite/Postgres console | Fork-safe setup requires split `pull_request` -> `workflow_run` token dance or read-only public project clones | Strong metric dimensions (latency, memory, file size) via `bencher_adapter` (`json` / `custom`) | `bencher_boundary` (`lib/bencher_boundary/src/boundary.rs`) supports Student's t-test, IQR, Mann-Whitney, and static limits | Core CLI `MIT OR Apache-2.0`, but `plus/*` (`LICENSE-PLUS`) is source-available proprietary; hosted SaaS dependency unless self-hosting a server |
| **`CodSpeed` (`action v5.8.0`, `b1f28b5ecc...`)** | SaaS platform (`codspeed.io`) via OIDC / upload token | Fork PRs supported via tokenless OIDC on public repos, but uploads telemetry to external SaaS | Designed for `Criterion`/`Divan` Rust harnesses (`codspeed-rust`) or `simulation`/`walltime`/`memory` modes; awkward for `.olean` multi-part artifact censuses | Excellent microbenchmark determinism via Valgrind Cachegrind CPU simulation (`Ir` / `CEst` `< 0.1%` CV), but **`15x`–`359x` slowdown** makes full Lean/Rust compiler runs impractical | Action `MIT` / Rust crate `Apache-2.0`; backend, dashboard, and history storage are proprietary SaaS |
| **`rustc-perf` (`15d9590542...`)** | Dedicated Postgres/SQLite backend + `perf.rust-lang.org` web server + bare-metal collector queue | Uses `@bors` / `@rust-timer` authorized try-builds on dedicated hardware rather than shared GitHub-hosted runners | `28` built-in `rustc` metrics (`instructions:u`, `max-rss`, `size:linked_artifact`, `-Zself-profile` `.mm_profdata`) | 30-commit historical adjacent-delta IQR fence $Q_3 + 3.0\,\text{IQR}$ (`site/src/comparison.rs:1238-1347`); headline filtered arithmetic mean has inversion bias | `MIT OR Apache-2.0`, but requires persistent database + dedicated runner daemon |

**Live Historical Evidence in `google/zerocopy`:**
- At `google/zerocopy@962a5a3a82822f05b6201d475e737a1615f28f3e`, `.github/workflows/anneal.yml` used `benchmark-action/github-action-benchmark@a60cea5bc7b49e15c1f58f411161f99e0df48372` (`v1.22.0`) to push `Docker Build Time`, `Docker Image Size`, and `CI Durations` into `dashboard/data.js` on the orphan `benchmark-data` branch (`d07175ed40ac6605442525427efbd86c76f8b199`: `842,457 B` `dashboard/data.js` across `416` commits of just `4` scalar series, plus `8,725 B` `dashboard/index.html` loading unpinned `chart.js@2.9.2` from `cdn.jsdelivr.net`).
- At `google/zerocopy@d74fc66829d3cdc5d374c37de2ee46c22b2153b4`, retiring the legacy V1/V2 workflow removed the `github-action-benchmark` writers while `.github/workflows/docs.yml:202-221` (`d3362d9a657e2f943d25a0812f7b13b93e60af4d`) **retained** the exact fork-safe GitHub Pages mount step: checking out `ref: benchmark-data` into `temp-bench` (`persist-credentials: false`) and copying `../temp-bench/dashboard/*` to `target/doc/bench/` (`https://google.github.io/zerocopy/bench/`). Generating a self-contained static dashboard into `dashboard/` on `benchmark-data` (or under `dashboard/anneal/`) therefore integrates directly with existing exact-SHA-gated GitHub Pages deployment with zero new deployment tokens or infrastructure.

---

### 2. Wire-Format Scaling and Concurrent Orphan-Branch Storage Protocol

`Basis: source + execution (support/verify_ci_perf_tracking.py, Probe 1) + derived`

Evaluating long-horizon Git repository bloat across `2,000` commits $\times$ `60` tracked metrics (`120,000` scalar observations) in `Probe 1` demonstrates an order-of-magnitude gap between `github-action-benchmark`'s denormalized `data.js` schema and a two-layer **append-only `JSONL` source-of-truth + generated columnar `dashboard/data.json`** layout:

| Format (`2,000` commits $\times$ `60` metrics) | Uncompressed Bytes | `gzip -9` Bytes | Raw Ratio vs. Columnar | Gzip Ratio vs. Columnar | Git Packfile & Diff Behavior |
| :--- | ---: | ---: | ---: | ---: | :--- |
| **`github-action-benchmark` `data.js` (indented)** | `16,711,217 B` (`15.94 MiB`) | `628,662 B` (`613.9 KiB`) | `15.96x` | `22.09x` | Rewrites multi-MiB JS blob every commit; repeats commit author/URL/metric metadata `60x` |
| **Canonical append-only `records.jsonl` (`1` line/commit)** | `4,205,071 B` (`4.01 MiB`) | `58,947 B` (`57.6 KiB`) | `4.02x` | `2.07x` | Strictly append-only (`O(1)` line diff per commit); Git packfile delta compression stores incremental lines in `< 2 KiB`/commit |
| **Columnar dashboard JSON (`commits` + `metrics` + `series`)** | `1,047,006 B` (`1.00 MiB`) | `28,456 B` (`27.8 KiB`) | `1.00x` | `1.00x` | Browser-ready dense typed arrays; `27.8 KiB` over HTTP gzip for `2,000` commits of `60` metrics |

**Concurrent Writer Safety on an Orphan Data Branch:**
- `github-action-benchmark` (`src/write.ts:413-450`) documented push contention failures when concurrent CI jobs update `benchmark-data` simultaneously.
- A dedicated collector workflow avoids loss or corruption via two complementary controls:
  1. **Workflow-level serialization:** `concurrency: { group: anneal-perf-tracking, cancel-in-progress: false }` queues `main` pushes cleanly without cancelling an in-flight measurement run.
  2. **Idempotent SHA-keyed append + bounded CAS retry:** Before committing to `benchmark-data`, the writer fetches `origin/benchmark-data`, reads `anneal/records.jsonl`, replaces or skips any existing record with matching `(source_sha, runner_profile, schema_version)` (idempotency on workflow reruns), appends the new canonical JSON line, regenerates `dashboard/`, commits, and pushes with a bounded `git fetch` + replay retry loop (`max_attempts = 5`).

---

### 3. Visualization Substrates and HTML5 `<script>` Escape Invariants

`Basis: source + execution (support/verify_ci_perf_tracking.py, Probe 4)`

Inspecting upstream release artifacts and rendering models across candidate charting libraries establishes a clear split for static verification dashboards:

1. **External CDN hazard (`github-action-benchmark` default `index.html`):** `benchmark-data:dashboard/index.html:107` loads `https://cdn.jsdelivr.net/npm/chart.js@2.9.2/dist/Chart.min.js` with no `integrity="sha384-..."` attribute, relies on undocumented `Chart.js` v2 private internals (`activeElems[0]._index`, line `239`), and renders `N` separate `<canvas>` elements stacked vertically with no search, metric grouping, commit-range zoom, or baseline comparison table.
2. **Third-party library footprint comparison:**
   - **Zero-dependency custom SVG/Canvas renderer (`~15`–`25 KiB` unminified, `~5`–`8 KiB` gzipped):** Inline SVG `<polyline>` / `<path>` overview sparklines paired with an interactive HTML5 `<canvas>` / SVG detail chart (supporting hover crosshair, click-to-open GitHub commit URL, drag/preset commit-window zoom `Last 50 / 200 / All`, dual-metric overlay, search/category filter, and rolling `Median ± MAD` band) require zero external dependencies, zero npm build step, and zero license/SRI maintenance.
   - **Vendored `uPlot 1.6.32` (`leeoniya/uPlot@a8b48ee3a2ec53700194155fbfd8db71e0ca9fef`, MIT):** `dist/uPlot.iife.min.js` is `80,073 B` (`~25 KiB` gzip) plus `dist/uPlot.min.css` (`3,159 B`); strong choice when plotting `> 50,000` simultaneous points on a single canvas, though still requiring vendoring `83 KiB` of third-party minified JS/CSS.
   - **`Chart.js v4.6.1` (`chartjs/Chart.js@ff1bdc38a102e7b9e97756041b1118272ed08564`, MIT) and `Vega-Lite v6.5.0` (`vega/vega-lite@9d3a9a2e87ebbae0a525f1169b85b82fed986a21`, BSD-3-Clause):** `Chart.js` v4 UMD builds exceed `200 KiB` minified, and `Vega-Lite` requires `vega` + `vega-lite` + `vega-embed` (`> 1.1 MiB` minified JS), disproportionately dwarfing the `28 KiB` compressed dataset itself.
3. **HTML5 script-data breakout invariant (`Probe 4`):** When bundling `data.json` into a standalone offline-viewable `index.html` (e.g., `<script id="perf-data" type="application/json">...</script>` or `window.PERF_DATA = ...;`), raw `json.dumps(payload)` is **vulnerable to HTML injection / XSS** if an untrusted commit message or benchmark label contains `</script>` (case-insensitive), because the HTML5 tokenizer terminates the `<script>` element before the JavaScript or JSON parser runs. Replacing `<`, `>`, `&`, `U+2028`, and `U+2029` with `\u003c`, `\u003e`, `\u0026`, `\u2028`, and `\u2029` preserves `100%` exact `JSON.parse` round-tripping while neutralizing script-tag breakouts (`Probe 4`).

---

### 4. Variance Control, Deterministic Proxies, and Regression-Detection Statistics

`Basis: source + execution (support/verify_ci_perf_tracking.py, Probe 2) + derived`

Shared cloud GitHub Actions runners (`ubuntu-24.04` 4-vCPU / 16 GiB VMs) do not expose hardware PMU instruction counters (`perf_event_open` `PERF_TYPE_HARDWARE` `instructions:u` returns `ENOENT` on virtualized guests without vPMU exposure) and exhibit two distinct noise regimes on wall-clock timings: baseline log-normal run-to-run jitter ($\sigma \approx 0.03$–$0.08$) and transient `~2`–`5%` noisy-neighbor tail spikes (`+25%` to `+55%` slowdown on a single run).

#### 4.1 Empirical Detector Comparison (`Probe 2`, `500` trajectories $\times$ `100` null steps + `+15%` permanent step)

| Detector Rule | $\sigma = 0.03$ FPR / 100c | $\sigma = 0.03$ TPR (`+15%`) | $\sigma = 0.08$ FPR / 100c | $\sigma = 0.08$ TPR (`+15%`) | Structural Behavior Under Shared-Runner Spikes |
| :--- | ---: | ---: | ---: | ---: | :--- |
| **`D1`: `github-action-benchmark` adjacent ratio ($x_t / x_{t-1} > 1.15$, $k=1$)** | `3.07` | `47.2%` | `13.06` | `49.4%` | **Unusable for alerting:** every transient spike (and recovery dip!) triggers false alerts |
| **`D2`: `rustc-perf` rolling $W=25$ adjacent-delta IQR fence ($k=1$)** | `2.99` | `37.6%` | `1.06` | `3.2%` | Fence widens dramatically as $\sigma$ rises, masking `+15%` step shifts (`3.2%` TPR at $\sigma = 0.08$) |
| **`D3`: Parametric rolling Mean + `3.5 SD` + `> 8%` ($k=1$)** | `2.58` | `44.8%` | `1.73` | `8.4%` | Single `+40%` outlier in the 25-commit window inflates sample SD $s$, blinding subsequent checks |
| **`D4`: In-job $k=3$ median + rolling $W=25$ `Median/MAD` ($z > 4.2 \land \Delta > 8\%$)** | **`0.34`** | **`98.0%`** | **`0.58`** | **`25.0%`** | $k=3$ median rejects single-run spikes (`0.03^2 = 0.09%` dual-spike rate); `1.4826 MAD` has `50%` breakdown point |
| **`D5`: $k=1$ 3-commit trailing median vs. rolling `Median/MAD` ($z > 4.2 \land \Delta > 8\%$)** | `0.35` | `95.0%` | `0.47` | `14.0%` | Achieves $k=3$ spike suppression at **`1x` CI compute cost** (`2`-commit detection lag) |
| **`D6`: In-job $k=3$ median + 2-commit sustained `Median/MAD` ($z_t, z_{t-1} > 3.5 \land \Delta > 8\%$)** | **`0.00`** | **`98.4%`** | **`0.02`** | **`17.0%`** | Near-zero false-alert rate (`<= 0.02` per `100` commits across all $\sigma$) with `98.4%` step recall at $\sigma = 0.03$ |

#### 4.2 Pairing Wall-Clock Telemetry With Zero-Variance Deterministic Proxies

Because wall-clock time on shared VMs cannot reliably catch `< 5%` algorithmic regressions in a single run, a verification benchmark suite should pair wall-clock timings (`capture`, `proof_and_audit`, `total`, and per-module `lean -j1` cold elaboration) with **deterministic (`CV = 0.00%`) structural proxies** emitted on the exact same build:
1. **Lean `.olean` part byte sizes (`.olean`, `.olean.server`, `.olean.private`):** Under Lean 4's `module` system, public `.olean` byte growth immediately flags accidental proof-term exposure (`@[expose]` / missing `private` encapsulation), while `.olean.private` byte growth directly tracks kernel proof-term bloat (`whnf` / `simp` / decision-procedure term blowups) with zero runner noise.
2. **Compiled binary and prebuilt archive sizes:** Stripped/release byte sizes of `cargo-anneal`, `anneal-rustc-capture`, `anneal-audit`, and the prebuilt `.olean` bundle (`manifest.json` total uncompressed and `.tar.zst` compressed bytes).
3. **Audit and proof graph cardinalities:** Audited declaration counts, `checkedAlternateProofs`, and verified unit counts (e.g., `zerocopy/proofs/` package unit counts and `capture` obligation counts).
4. **Symmetric multi-benchmark aggregation (`Probe 2`):** Summarizing a suite of $N$ benchmarks via arithmetic mean of percent changes $\frac{1}{N}\sum (B_i - A_i)/A_i$ reports **`+25.0%` regression** on a balanced `[2.0x, 0.5x]` pair in *both* forward ($A \to B$) and inverse ($B \to A$) directions. Dashboard suite summaries must use the **geometric mean of ratios**:
   $$\text{GeoMean}(B / A) = \exp\!\left(\frac{1}{N}\sum_{i=1}^{N} \ln\!\left(\frac{B_i}{A_i}\right)\right)$$
   which satisfies exact inversion symmetry $\text{GeoMean}(A / B) = \text{GeoMean}(B / A)^{-1}$ (`1.000000` on `[2.0x, 0.5x]`).

---

### 5. Linux `execve` `ru_maxrss` Inheritance Pitfall and Fresh-`exec` Shim Isolation

`Basis: source (torvalds/linux@65e4fd942f72a9dba0e4e257290c4fa1aa756854) + execution (support/verify_ci_perf_tracking.py, Probe 3)`

Tracking per-module `lean -j1` and verifier peak RSS (`ru_maxrss`) on Linux exposes a subtle kernel accounting mechanism in `torvalds/linux@65e4fd942f72a9dba0e4e257290c4fa1aa756854`:

1. **Kernel source mechanism (`kernel/fork.c` + `fs/exec.c`):**
   - During `execve`, `exec_mmap` (`fs/exec.c:843-913`) records `bprm->old_mm = old_mm` (`line 907`), and `exec_mm_put_old` (`fs/exec.c:916-921`) executes:
     ```c
     static void exec_mm_put_old(struct mm_struct *old_mm)
     {
         setmax_mm_hiwater_rss(&current->signal->maxrss, old_mm);
         mm_update_next_owner(old_mm);
         mmput(old_mm);
     }
     ```
     folding `max(old_mm->hiwater_rss, get_mm_rss(old_mm))` into `current->signal->maxrss`—the exact field returned as `ru_maxrss` by `wait4(2)` and `getrusage(RUSAGE_CHILDREN)`.
   - When a parent spawns a child via `fork()` (`!(clone_flags & CLONE_VM)`), `dup_mm` (`kernel/fork.c:1554`) sets `mm->hiwater_rss = get_mm_rss(mm)` at fork time. If the parent collector holds `128 MiB` of resident `MAP_PRIVATE` pages, `old_mm` carries `~128 MiB` into `exec_mm_put_old`, masking any child whose true peak RSS is `< 128 MiB`.
   - Worse, when a parent spawns a child via `vfork()` or `posix_spawn()` (`CLONE_VM | CLONE_VFORK`, used by Python 3.8+ `subprocess.Popen` on Linux), `copy_mm` (`kernel/fork.c:1598`) shares `current->mm` directly (`old_mm = parent->mm`). Even if the parent already freed (`munmap`) its `128 MiB` buffer before spawning the child, `parent->mm->hiwater_rss` retains the all-time `128 MiB` peak, which `exec_mm_put_old` permanently copies into the child's `signal->maxrss`!
   - Additionally, `getrusage(RUSAGE_CHILDREN)` reports the **maximum** `ru_maxrss` across all waited children of the calling process rather than per-child peak RSS.
2. **Live empirical confirmation (`Probe 3` on `x86_64` Linux):**
   Spawning `/bin/true` (true standalone RSS `~816 KiB`) from a Python parent that allocated `128 MiB` of `MAP_PRIVATE` memory:
   - `fork() + execv("/bin/true")` while mapped: `ru_maxrss = 139,052 KiB` (`170x` inflation);
   - `fork() + execv("/bin/true")` after `munmap`: `ru_maxrss = 8,008 KiB` (inherits Python interpreter's live RSS);
   - `subprocess.Popen(["/bin/true"])` (`posix_spawn` / `CLONE_VFORK | CLONE_VM`) **after `munmap`**: `ru_maxrss = 142,360 KiB` (**`174x` inflation from historical parent peak!**);
   - Spawning via `/usr/bin/time -f "%M" /bin/true` (where `/usr/bin/time` `execve`s first into a `~1.5 MiB` `mm_struct` and then `fork+exec+wait4`s `/bin/true`): **`816 KiB`** (exact true child peak RSS, completely immune to parent RSS).
3. **Collector design rule:** Any Python or Rust benchmark harness measuring subprocess `ru_maxrss` on Linux must either (a) invoke targets via `/usr/bin/time` (or a minimal `< 2 MiB` helper binary that `exec`s before `fork+exec+wait4`ing the target), or (b) keep the parent collector's historical and resident RSS strictly below the smallest measured target (`< 15 MiB`) and use explicit `fork() + execve()` + per-PID `os.wait4(pid, 0)` rather than `subprocess.Popen` (`posix_spawn`) or `RUSAGE_CHILDREN`.

## Boundaries

- **Not examined:**
  - Dedicated bare-metal self-hosted GitHub Actions runners with CPU frequency governors locked (`cpupower frequency-set -g performance`), SMT disabled, and hardware PMU counters (`PERF_TYPE_HARDWARE` `instructions:u` / `cycles:u`) enabled via `perf_event_paranoid <= 1`.
  - macOS (`Mach` `task_info` / `rusage_info_v4` `ri_phys_footprint`) and Windows Job Object peak memory accounting semantics under process creation.
  - Browser WebGL rendering libraries (such as `echarts-gl` or `deck.gl`), which are unnecessary for `< 250,000` 2D time-series points.
- **Unknown:**
  - Future GitHub-hosted `ubuntu-24.04` / `ubuntu-26.04` underlying hypervisor CPU SKU migrations (e.g., AMD EPYC generation shifts on Azure host pools), which can introduce step shifts in raw wall-clock series without any repository commit change; recording CPU model strings (`/proc/cpuinfo` `model name`) in every benchmark record allows step shifts from runner hardware changes to be attributed rather than misdiagnosed as code regressions, though exact future SKU schedules remain unknown.
- **Known not to apply:**
  - Using `github-action-benchmark`'s single-commit ratio detector (`alert-threshold` with `fail-on-alert: true`) as a merge-blocking CI gate on shared GitHub-hosted runners: `Probe 2` demonstrates `3.07`–`21.74` false failures per `100` commits under realistic shared-runner variance.
  - Reading per-child peak RSS on Linux via `subprocess.Popen` + `os.wait4` inside a memory-intensive Python/Rust driver: `Probe 3` and `fs/exec.c:918` prove that `CLONE_VM` `posix_spawn` contaminates child `ru_maxrss` with the parent's all-time `hiwater_rss` whenever `parent_hiwater_rss > child_true_rss`.
  - Arithmetic means of percentage changes $\frac{1}{N}\sum (B_i - A_i)/A_i$ for bidirectional multi-benchmark summaries (`+25.0%` positive bias on `[2.0x, 0.5x]`).
- **Unsupported:**
  - Unprivileged hardware CPU instruction-retired counters (`PERF_TYPE_HARDWARE` `PERF_COUNT_HW_INSTRUCTIONS`) on standard virtualized GitHub-hosted Linux runners that do not expose an architectural vPMU (`perf_event_open` returns `ENOENT`).
  - Granting `contents: write` or `pages: write` to `pull_request` workflows triggered from external repository forks on GitHub Actions (GitHub forcefully downgrades fork `GITHUB_TOKEN` permissions to read-only, causing push-based benchmark steps in `pull_request` jobs to fail with HTTP `403`).

## Evidence

- **Primary upstream repositories and source locations (`observed_at: 2026-11-23`):**
  - `google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d`:
    - `.github/workflows/docs.yml:19-260` (exact-SHA two-workflow `coordinate` gate, `ref: benchmark-data` checkout to `temp-bench` at lines `202-221`, `target/doc/bench` copy, and `actions/deploy-pages@368f82528645a54fb793d4d04e342629a3f51346`);
    - `.github/workflows/ci.yml:1219-1239` (`zizmorcore/zizmor-action@53290badfa369cb0bf7ad16342cb62c2fa47ac7b` configured with `persona: pedantic`, `min-severity: medium`, `advanced-security: false`);
    - `.github/workflows/anneal-current.yml:1-140` (`permissions: { contents: read }`, stripped `ACTIONS_CACHE_URL`/`ACTIONS_RUNTIME_TOKEN` in `static-checks`);
    - `anneal/trusted/cargo-anneal/src/verify.rs:1878-1903` (Receipt v3 `timing_ms: { capture, proof_and_audit, total }`);
    - `anneal/trusted/cargo-anneal/src/olean_cache.rs:66-250` and `anneal/ci/prebuild_bundled_oleans.py:1-90` (landed in `ff55d9d48f95acca17275bea53dcb3145f5225a5`, content-addressed `OleanCacheKeyInput` and 3-part `OLEAN_PARTS = ("olean", "olean.server", "olean.private")` prebuilder);
    - `anneal/ci/verify_zerocopy.py:280-335` (`zerocopy/proofs/` per-package `wall_seconds` and receipt harness);
    - Historical commits `962a5a3a82822f05b6201d475e737a1615f28f3e` (legacy `github-action-benchmark` setup) and `d74fc66829d3cdc5d374c37de2ee46c22b2153b4` (V1/V2 removal), plus `refs/heads/benchmark-data` @ `d07175ed40ac6605442525427efbd86c76f8b199` (`dashboard/data.js` `842,457 B`, `dashboard/index.html` `8,725 B`).
  - `benchmark-action/github-action-benchmark@84ec6ea748925b6580796c05ce7a1c8fd0d15f3b` (`v1.22.2`): `src/write.ts:21, 98-120, 273-335, 413-450` (`window.BENCHMARK_DATA` format, single-commit `findAlerts` ratio check, `git.push` retry/warning logic, and default `Chart.js` `2.9.2` jsDelivr template).
  - `bencherdev/bencher@a39a1f4fb7d2a0bffcfc2d4d044852072ce98358` (`v0.6.17`): `LICENSE.md:1-12` (`plus/` Bencher Plus License vs. `MIT OR Apache-2.0`), `action.yml:1-60`, and `lib/bencher_boundary/src/{boundary.rs,mean.rs,quartiles.rs}`.
  - `CodSpeedHQ/action@b1f28b5eccf7cb5bfe6a2a89cb3053eb67f1150c` (`v5.8.0`): `action.yml:1-75` (`simulation`, `walltime`, `memory` modes and SaaS upload endpoint) and `CodSpeedHQ/codspeed-rust@6ab62f6d0545adf2052e413e349c8b529904e575` (`v6.1.0`).
  - `rust-lang/rustc-perf@15d95905429e577d5a710b17c49e04b4451c263b`: `site/src/comparison.rs:346-513, 1232-1443` and `site/frontend/src/pages/compare/data.ts:86-136` (30-commit historical IQR threshold and filtered arithmetic-mean summary).
  - `zizmorcore/zizmor@0b77258cf93d4e0ae762c843422c333faf2793f6` (`v1.23.1`): executed offline with `--persona pedantic` across three workflow topologies (`pull_request_target` + `contents: write` -> exit `14` with `2` High/Medium errors; undocumented job-level `contents: write` without `concurrency` -> exit `12`; isolated `push: [main]` + `schedule` + `workflow_dispatch` with `permissions: {}`, documented job `contents: write`, `concurrency`, `persist-credentials: false`, and pinned action SHAs -> exit `0`, `0` findings).
  - `leeoniya/uPlot@a8b48ee3a2ec53700194155fbfd8db71e0ca9fef` (`1.6.32`, `dist/uPlot.iife.min.js` `80,073 B`, `dist/uPlot.min.css` `3,159 B`), `chartjs/Chart.js@ff1bdc38a102e7b9e97756041b1118272ed08564` (`v4.6.1`), and `vega/vega-lite@9d3a9a2e87ebbae0a525f1169b85b82fed986a21` (`v6.5.0`).
  - `torvalds/linux@65e4fd942f72a9dba0e4e257290c4fa1aa756854`: `kernel/fork.c:1554, 1575-1618` (`dup_mm` `hiwater_rss = get_mm_rss(mm)` vs. `CLONE_VM` shared `mm_struct`) and `fs/exec.c:906-921` (`exec_mm_put_old` `setmax_mm_hiwater_rss(&current->signal->maxrss, old_mm)`).
  - `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`): `.olean` / `.olean.server` / `.olean.private` module serialization artifacts.
- **Preserved standalone verification package material:**
  - `reports/ci-performance-tracking-fork-safe-github-pages-dashboards-and-regression-detection/support/verify_ci_perf_tracking.py` (SHA-256: `6cd7539f8f3d45d98653ee22980921d061e31041f62cdde624947a326a160b96`), deterministic Python 3.10+ standard-library verification suite covering `Probe 1` (`storage_scaling`), `Probe 2` (`regression_detectors`), `Probe 3` (`linux_maxrss_accounting`), and `Probe 4` (`security_and_html_invariants`).

## Revalidation

1. **Rerun the preserved deterministic 4-probe verification suite (`< 2.0 s`, Python 3.10+ stdlib only):**
   ```bash
   PYTHONHASHSEED=1 python3 -I -B reports/ci-performance-tracking-fork-safe-github-pages-dashboards-and-regression-detection/support/verify_ci_perf_tracking.py
   PYTHONHASHSEED=2 python3 -I -B reports/ci-performance-tracking-fork-safe-github-pages-dashboards-and-regression-detection/support/verify_ci_perf_tracking.py
   ```
   Verify script SHA-256 `6cd7539f8f3d45d98653ee22980921d061e31041f62cdde624947a326a160b96`, exit code `0`, and bit-identical `3,485`-byte JSON stdout with SHA-256 `f5fae46d6a5e595620922cbf6889bbcecf9613d9c07413f33355dedd4cc0273a`. This revalidates the wire-size ratios (`15.96x` raw / `22.09x` gzip), Monte Carlo detector FPR/TPR matrix, geomean inversion symmetry, Linux `exec_mm_put_old` `ru_maxrss` model (plus live `MAP_PRIVATE` `fork` vs. `posix_spawn` kernel behavior on Linux hosts), and HTML5 `</script>` breakout neutralization.
2. **Revalidate GitHub Actions workflow security under newer `zizmor` releases:**
   ```bash
   zizmor --persona pedantic --offline .github/workflows/<perf-workflow>.yml
   ```
   Confirm `0` findings at `medium`+ severity (and `0` undocumented permissions or missing concurrency groups under `pedantic`).
3. **Revalidate Linux kernel `execve` `ru_maxrss` semantics on newer kernels:**
   Diff `fs/exec.c` around `exec_mm_put_old` (`setmax_mm_hiwater_rss(&current->signal->maxrss, old_mm)`) and `kernel/fork.c` around `copy_mm` / `dup_mm`, or run `/usr/bin/python3` Probe 3 directly on the target kernel to check whether `posix_spawn` (`CLONE_VM | CLONE_VFORK`) still folds parent `hiwater_rss` into `wait4` `ru_maxrss`.

*Authored by an AI agent acting on joshlf's behalf.*
