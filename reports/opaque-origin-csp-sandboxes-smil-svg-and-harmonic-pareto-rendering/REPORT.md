<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Opaque-Origin CSP Sandboxes, Zero-JS SMIL SVG, and Harmonic Pareto Rendering

## Summary

Static benchmark reports served inside sandboxed iframe viewers (`Origin: null`,
strict CSP) break silently when inline scripts call unguarded `localStorage`,
load remote CDNs, or embed unencoded `data:image/svg+xml;utf8,` URIs containing
`#` hex colors. Pairing pre-hydrated static HTML and RFC 2397 base64 SMIL SVGs
eliminates scripting failures, while replacing linear or straight semi-log
Pareto chords with harmonic time-sharing curves (`((1-f)/v0 + f/v1)^-1`) avoids
overstating throughput by `+52.8%` to `+133.5%` and eliminates real dominance
inversions (`-4.21%` to `+37.04%`) on compression frontiers.

## Applicability

- Static HTML visualization bundles hosted in opaque-origin (`Origin: null`)
  artifact sandboxes with strict CSP (`sandbox`, no external network access).
- Declarative SMIL 3.0 / SVG 1.1 animations rendered inside HTML `<img>` elements
  under W3C SVG Integration animated-image mode (scripts suppressed).
- Plotting speed-vs.-ratio Pareto trade-offs for time-shared operating points.

## Findings

### Opaque-Origin (`Origin: null`) and Strict CSP Constraints

1. **`localStorage` Access Requires `try/catch` Guards and Pre-Hydration:** In a
   sandboxed viewer lacking `allow-same-origin`, `window.origin` evaluates to the
   serialized opaque origin `"null"`, causing synchronous reads or writes on
   `window.localStorage` to throw `SecurityError` and abort remaining script
   execution. Wrapping every `localStorage` reference inside `try { ... } catch
   (_) {}` alongside an inline pre-hydrated `<html data-theme="...">` attribute
   keeps light/dark theme switching functional without blocking page load.
2. **Hermetic Inlining vs. Unencoded UTF-8 `data:` URIs:** Under strict CSP,
   remote scripts, stylesheets, CSS `@import`, `fetch()`, and `<object>` /
   `<embed>` / `<iframe>` fail blocked-load checks. Encoding SVG plots via
   strict `[A-Za-z0-9+/=]` base64 (`data:image/svg+xml;base64,...` per RFC 2397)
   instead of raw UTF-8 prevents `#` hex colors (such as `#ffffff` or `#d62728`)
   from truncating the data URI at the RFC 3986 fragment delimiter.

### Zero-JavaScript SMIL 3.0 and SVG 1.1 Structural Invariants

When an animated SVG sits inside `<img src="data:image/svg+xml;base64,...">`,
browsers execute it in W3C SVG Integration animated-image mode with JavaScript
disabled (`0` `<script>` nodes, `0` `on*` handlers, `0` `javascript:` URIs):

1. **Boundary Holds and Monotonic `keyTimes`:** Every `calcMode="linear"`
   `<animate>` element must keep `keyTimes` monotonically non-decreasing across
   `[0, 1]` with `keyTimes[0] == 0` and `keyTimes[-1] == 1`. Duplicating first
   and last frame values enforces explicit boundary pauses (`HOLD_FIRST = 1.4s`,
   `HOLD_LAST = 3.0s` in a `6.1s` loop) without interpolating across loop wrap.
2. **Isomorphic `<path d>` Command Topology:** W3C SVG 1.1 Section 19.2.15
   silently drops path morphing if two keyframes differ in command structure.
   Clamping unintroduced levels to their first-seen operating point keeps every
   `attributeName="d"` keyframe strictly isomorphic (`["M"] + ["L"] * 16`).
3. **Trajectory Trails and Partition-of-Unity Discrete Tickers:** Trajectory
   trails animate `stroke-dashoffset` monotonically non-increasing down to `0.0`
   with matching `stroke-dasharray`, while per-frame caption lines animate
   `opacity` via `calcMode="discrete"` forming an exact partition of unity
   (`sum == 1` across `[0, 1)`).

### Harmonic Time-Sharing Curves vs. Linear and Semi-Log Chords

When an engine mixes byte fractions `(1 - f, f)` between operating points `(r0,
v0)` and `(r1, v1)`, byte-weighted ratio moves linearly `(1 - f)r0 + f*r1` while
effective throughput `v_harm(f)` is the weighted **harmonic** mean `((1 - f)/v0 +
f/v1)^-1`:

1. **Exact AM-GM-HM Overstatement Laws:** Whenever `v0 != v1` (`rho =
   max(v0,v1)/min(v0,v1)`) and `0 < f < 1`, AM-GM-HM enforces `v_harm(f) <
   v_log(f) < v_lin(f)` strictly (`max_formula_discrepancy = 3.55e-14`), where
   `v_log(f) = v0^(1-f) * v1^f` is a straight segment on a logarithmic-Y chart
   and `v_lin(f)` is linear interpolation. Relative error peaks at `f = 1/2` at
   `(rho - 1)^2 / (4 * rho)` for linear chords and `(sqrt(rho) - 1)^2 /
   (2 * sqrt(rho))` for semi-log chords; absolute linear error peaks at
   `(sqrt(v0) - sqrt(v1))^2` when `f* = sqrt(v1) / (sqrt(v0) + sqrt(v1))`. Across
   `lean_zip_2f7a63f L8->L9` (`18.36 -> 2.55 MiB/s`, `rho = 7.20`), a linear
   chord inflates throughput by `+133.47%` (`7.23 MiB/s`), and even a straight
   semi-log chord inflates by `+52.80%` (`47.24 px` vertical error in a `940 x
   660` viewBox), which `n=16` tessellation cuts `34.6x` to `1.37 px` (and
   `78.2x` from `17.59 px` to `0.225 px` on Rust `L8->L9`).
2. **Real Silesia False-Dominance Inversions:** Evaluating the single-core 2 MiB
   Silesia curves reveals operating points where straight chords falsely report
   Pareto inferiority despite genuine harmonic superiority:

| Subject Point | Reference Chord | True Gain vs. Harmonic | Misread Linear (Semi-Log) |
| :--- | :--- | :--- | :--- |
| `lean_zip_2f7a63f L5` (`34.00`) | `miniz_oxide_0_9_1 L5->L6` (`33.66`) | `+1.01%` | `-2.60%` (`34.91` lin / `34.32` log) |
| `rust_safe_hash4_bt L2` (`140.90`) | `rust_unsafe_bt_dp_simd L1->L2` (`140.70`) | `+0.14%` | `-4.21%` (`147.09` lin / `143.52` log) |
| `rust_unsafe_bt_dp_simd L7` (`17.61`) | `rust_safe_hash4_bt L8->L9` (`12.85`) | `+37.04%` | `-0.39%` (`17.68` lin) |
| `rust_unsafe_row_hash_simd L8` (`10.99`) | `rust_safe_hash4_bt L8->L9` (`8.77`) | `+25.38%` | `-1.41%` (`11.15` lin) |
| `miniz_oxide_0_9_1 L8` (`16.69`) | `zlib_1_3_2 L7->L8` (`16.21`) | `+2.98%` | `-0.36%` (`16.75` lin) |

## Boundaries

- HTML/SMIL checks cover structural static invariants (`Origin: null`, strict
  CSP, W3C SVG 1.1 / SMIL 3.0 schema, and `data:` encoding) enforced by parsing;
  browser engine rendering differences across specific versions are not invoked.
- Concrete inversion table entries depend on the single-core 2 MiB Silesia
  benchmark points imported from the companion benchmark package.

## Evidence

| Check | Verified Outcome | Artifact |
| :--- | :--- | :--- |
| SMIL 3.0 & SVG 1.1 audit | `38` anims (`35` lin, `3` disc, `8` `d`, `9` dash) | [sandbox_csp_smil_harmonic_probe.py](support/sandbox_csp_smil_harmonic_probe.py) |
| `Origin: null` & CSP check | `26,534 B` HTML, `26,180 B` b64, guarded `localStorage` | [sandbox_csp_smil_harmonic_probe.py](support/sandbox_csp_smil_harmonic_probe.py) |
| Closed-form AM-GM-HM error | `max_formula_discrepancy = 3.55e-14`; `+133.47%` lin | [sandbox_csp_smil_harmonic_probe.py](support/sandbox_csp_smil_harmonic_probe.py) |
| Pareto inversion & `n=16` SVG | `5` inversions verified; `34.6x-152.8x` pixel error drop | [sandbox_csp_smil_harmonic_probe.py](support/sandbox_csp_smil_harmonic_probe.py) |

## Revalidation

Run the self-contained validator inside `support/` and confirm `exit 0`:

```bash
python3 support/sandbox_csp_smil_harmonic_probe.py
```
