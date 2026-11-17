#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Standalone verification probe for:
1. Opaque-Origin (`Origin: null`, WHATWG HTML `sandbox`) & strict CSP static
   HTML bundle invariants (guarded `localStorage`, zero external HTTP(S)
   scripts/stylesheets/fonts/fetches, RFC 2397 `data:image/svg+xml;base64,`
   integrity).
2. Zero-JavaScript SMIL 3.0 / SVG 1.1 declarative animation invariants inside
   `<img>`-referenced SVGs (W3C SVG Integration animated-image mode,
   `calcMode="linear"` endpoint-held `keyTimes` in `[0, 1]`, `<path d>` command
   isomorphism across keyframes, monotonic `stroke-dashoffset` trail reveal, and
   `calcMode="discrete"` HUD ticker partition of unity).
3. Analytical and empirical verification of Harmonic Time-Sharing Pareto Curves
   (`v(f) = ((1-f)/v0 + f/v1)^-1`) vs. naive linear chords (`(1-f)v0 + f*v1`)
   and semi-log straight chords (`v0^(1-f) * v1^f`), including false Pareto
   dominance inversions across quiet single-core Silesia `L1..L9` profiles.

Run standalone (standard library only):
  python3 sandbox_csp_smil_harmonic_probe.py
"""

from __future__ import annotations

import argparse
import base64
from html import escape
from html.parser import HTMLParser
import json
import math
from pathlib import Path
import re
import sys
import xml.etree.ElementTree as ET

SVG_NS = "http://www.w3.org/2000/svg"
SVG_W, SVG_H = 940, 660
SVG_ML, SVG_MR, SVG_MT, SVG_MB = 72, 18, 70, 72
FRAME_SECONDS = 0.85
HOLD_FIRST = 1.4
HOLD_LAST = 3.0

# 12-file Silesia 2 MiB quiet single-core (`taskset -c 4`) geomean operating
# points `(level, gm_ratio, compress_mibs, decompress_mibs)` matching Package 8.
EMBEDDED_SERIES: dict[str, list[tuple[int, float, float, float]]] = {
    "miniz_oxide_0_9_1": [
        (1, 0.462660, 136.82, 269.44),
        (2, 0.391401, 76.50, 343.60),
        (3, 0.364116, 53.00, 387.00),
        (4, 0.360648, 47.70, 373.60),
        (5, 0.355380, 38.40, 375.70),
        (6, 0.349223, 24.80, 387.20),
        (7, 0.347794, 19.90, 397.40),
        (8, 0.347037, 16.69, 404.54),
        (9, 0.346682, 15.18, 392.96),
    ],
    "zlib_1_3_2": [
        (1, 0.405012, 80.03, 306.47),
        (2, 0.391785, 72.84, 317.71),
        (3, 0.378519, 55.98, 335.07),
        (4, 0.370084, 52.63, 323.26),
        (5, 0.357816, 35.73, 325.70),
        (6, 0.350783, 25.02, 328.50),
        (7, 0.348573, 20.98, 335.98),
        (8, 0.346169, 14.36, 338.90),
        (9, 0.345735, 13.12, 340.13),
    ],
    "lean_zip_2f7a63f": [
        (1, 0.418992, 163.49, 243.53),
        (2, 0.383104, 104.80, 272.70),
        (3, 0.366727, 57.80, 289.30),
        (4, 0.358529, 45.20, 265.90),
        (5, 0.353799, 34.00, 251.10),
        (6, 0.349916, 24.10, 237.94),
        (7, 0.347779, 25.40, 258.40),
        (8, 0.345073, 18.36, 250.77),
        (9, 0.341448, 2.55, 184.04),
    ],
    "rust_safe_hash4_bt": [
        (1, 0.412940, 219.02, 439.44),
        (2, 0.378828, 140.90, 534.10),
        (3, 0.363587, 77.50, 572.00),
        (4, 0.355586, 60.00, 556.70),
        (5, 0.349956, 42.70, 552.20),
        (6, 0.346004, 34.14, 550.64),
        (7, 0.344650, 29.90, 544.70),
        (8, 0.343630, 24.28, 538.52),
        (9, 0.334858, 7.42, 529.20),
    ],
    "rust_safe_row_hash_bt": [
        (1, 0.413167, 171.67, 429.49),
        (2, 0.381267, 131.20, 517.90),
        (3, 0.362755, 73.90, 517.30),
        (4, 0.356200, 62.00, 533.40),
        (5, 0.353168, 45.30, 522.60),
        (6, 0.348747, 37.97, 538.66),
        (7, 0.346506, 30.00, 514.20),
        (8, 0.344680, 25.89, 544.16),
        (9, 0.337663, 7.69, 527.28),
    ],
    "rust_unsafe_bt_dp_simd": [
        (1, 0.414186, 220.24, 519.45),
        (2, 0.370276, 129.40, 608.20),
        (3, 0.359500, 85.80, 621.20),
        (4, 0.353240, 60.70, 629.90),
        (5, 0.349079, 51.60, 631.40),
        (6, 0.345549, 37.21, 621.76),
        (7, 0.340196, 17.61, 613.50),
        (8, 0.336545, 10.69, 628.95),
        (9, 0.333358, 6.68, 616.83),
    ],
    "rust_unsafe_row_hash_simd": [
        (1, 0.417898, 214.55, 520.97),
        (2, 0.377435, 117.20, 592.00),
        (3, 0.362266, 77.20, 581.30),
        (4, 0.355312, 61.20, 598.30),
        (5, 0.351513, 52.20, 621.10),
        (6, 0.347266, 36.43, 602.82),
        (7, 0.344792, 25.20, 602.70),
        (8, 0.336797, 10.99, 617.35),
        (9, 0.332132, 5.53, 626.76),
    ],
}


def sx(r: float, xlim: tuple[float, float] = (0.325, 0.470)) -> float:
    return SVG_ML + (r - xlim[0]) / (xlim[1] - xlim[0]) * (SVG_W - SVG_ML - SVG_MR)


def sy(v: float, ylim: tuple[float, float] = (2.0, 320.0)) -> float:
    return (
        SVG_H
        - SVG_MB
        - (math.log10(v) - math.log10(ylim[0]))
        / (math.log10(ylim[1]) - math.log10(ylim[0]))
        * (SVG_H - SVG_MT - SVG_MB)
    )


def mix_d(
    x0: float,
    y0: float,
    x1: float,
    y1: float,
    n: int = 16,
    xlim: tuple[float, float] = (0.325, 0.470),
    ylim: tuple[float, float] = (2.0, 320.0),
) -> str:
    """Render an n-segment SVG path string along the harmonic time-sharing curve."""
    pts = []
    for i in range(n + 1):
        f = i / n
        r = (1.0 - f) * x0 + f * x1
        v = 1.0 / ((1.0 - f) / y0 + f / y1)
        pts.append(("M" if i == 0 else "L") + f"{sx(r, xlim):.1f},{sy(v, ylim):.1f}")
    return "".join(pts)


def synthesize_smil_svg(frames_pts: list[dict]) -> str:
    """Synthesize a self-playing zero-JS SMIL SVG with uniform path topology."""
    n_frames = len(frames_pts)
    total_dur = HOLD_FIRST + FRAME_SECONDS * max(n_frames - 1, 1) + HOLD_LAST
    starts = [HOLD_FIRST + FRAME_SECONDS * i for i in range(n_frames)]
    keytimes = [0.0] + [s / total_dur for s in starts] + [1.0]

    def keyframes(vals: list[str]) -> tuple[str, str]:
        seq = [vals[0]] + list(vals) + [vals[-1]]
        return ";".join(seq), ";".join(f"{k:.5f}" for k in keytimes)

    def anim(attr: str, vals: list[str]) -> str:
        v_s, k_s = keyframes(vals)
        return (
            f'<animate attributeName="{attr}" values="{v_s}" keyTimes="{k_s}" '
            f'calcMode="linear" dur="{total_dur:.1f}s" repeatCount="indefinite"/>'
        )

    levels = sorted({p[0] for f in frames_pts for p in f["points"]})
    pos = {lvl: [None] * n_frames for lvl in levels}
    for i, f in enumerate(frames_pts):
        for lvl, r, v in f["points"]:
            pos[lvl][i] = (r, v)
    first_seen = {lvl: next(i for i in range(n_frames) if pos[lvl][i]) for lvl in levels}

    def held(lvl: int) -> list[tuple[float, float]]:
        fs = first_seen[lvl]
        out_pts, last = [], pos[lvl][fs]
        for i in range(n_frames):
            if i >= fs and pos[lvl][i]:
                last = pos[lvl][i]
            out_pts.append(last)
        return out_pts

    out = [
        f'<svg xmlns="{SVG_NS}" viewBox="0 0 {SVG_W} {SVG_H}" '
        'font-family="Helvetica, Arial, sans-serif">',
        f'<rect width="{SVG_W}" height="{SVG_H}" fill="#ffffff"/>',
        f'<text x="{SVG_W/2:.0f}" y="28" text-anchor="middle" '
        'font-size="18.5" font-weight="bold" fill="#222222">'
        "Harmonic Time-Sharing Pareto Trajectory</text>",
    ]

    for lvl in levels:
        samples = [(i, pos[lvl][i]) for i in range(n_frames) if pos[lvl][i]]
        pts = [(sx(r), sy(v)) for _, (r, v) in samples]
        if len(pts) < 2:
            continue
        d = "M" + "L".join(f"{x:.1f},{y:.1f}" for x, y in pts)
        seg = [0.0]
        for (xa, ya), (xb, yb) in zip(pts, pts[1:]):
            seg.append(seg[-1] + math.hypot(xb - xa, yb - ya))
        total = seg[-1]
        if total <= 0:
            continue
        reveal, k = [], 0
        for i in range(n_frames):
            while k + 1 < len(samples) and samples[k + 1][0] <= i:
                k += 1
            reveal.append(seg[k] if samples[0][0] <= i else 0.0)
        out.append(
            f'<path d="{d}" fill="none" stroke="#d62728" stroke-width="1.3" '
            f'opacity="0.18" stroke-dasharray="{total:.1f} {total:.1f}" '
            f'stroke-dashoffset="{total:.1f}">'
        )
        out.append(anim("stroke-dashoffset", [f"{total - rv:.1f}" for rv in reveal]))
        out.append("</path>")

    for a, b in zip(levels, levels[1:]):
        ha, hb = held(a), held(b)
        ds = [mix_d(ha[i][0], ha[i][1], hb[i][0], hb[i][1]) for i in range(n_frames)]
        out.append(f'<path d="{ds[0]}" fill="none" stroke="#d62728" stroke-width="3.2" opacity="1">')
        out.append(anim("d", ds))
        out.append("</path>")

    for lvl in levels:
        h = held(lvl)
        cxs = [f"{sx(r):.1f}" for r, _ in h]
        cys = [f"{sy(v):.1f}" for _, v in h]
        out.append(f'<circle cx="{cxs[0]}" cy="{cys[0]}" r="6.6" fill="#d62728" opacity="1">')
        out.append(anim("cx", cxs))
        out.append(anim("cy", cys))
        out.append("</circle>")

    out.append('<g font-size="13.5" fill="#333333" font-family="Menlo, Consolas, monospace">')
    for i, f in enumerate(frames_pts):
        txt = escape(f"{f['tag']} ({i+1}/{n_frames}) - {f['label']}")
        s0 = starts[i] / total_dur
        s1 = starts[i + 1] / total_dur if i + 1 < n_frames else None
        if i == 0:
            vals, keys = "1;0", f"0;{s1:.5f}"
        elif s1 is None:
            vals, keys = "0;1", f"0;{s0:.5f}"
        else:
            vals, keys = "0;1;0", f"0;{s0:.5f};{s1:.5f}"
        out.append(
            f'<text x="{SVG_ML}" y="52" opacity="0">{txt}'
            f'<animate attributeName="opacity" values="{vals}" keyTimes="{keys}" '
            f'calcMode="discrete" dur="{total_dur:.1f}s" repeatCount="indefinite"/></text>'
        )
    out.append("</g>")
    out.append("</svg>")
    return "\n".join(out)


def verify_smil_svg_invariants(svg_text: str, label: str) -> dict:
    """Verify W3C SVG 1.1 & SMIL 3.0 structural, security, and timing invariants."""
    root = ET.fromstring(svg_text)
    assert root.tag == f"{{{SVG_NS}}}svg"
    assert root.attrib.get("viewBox") == f"0 0 {SVG_W} {SVG_H}"

    for elem in root.iter():
        local_name = elem.tag.split("}")[-1] if "}" in elem.tag else elem.tag
        assert local_name.lower() != "script", f"{label}: forbidden <script> inside SVG"
        for attr_name, attr_val in elem.attrib.items():
            bare_attr = attr_name.split("}")[-1].lower()
            assert not bare_attr.startswith("on"), f"{label}: forbidden event handler {attr_name}"
            assert "javascript:" not in attr_val.lower()

    anims = list(root.findall(f".//{{{SVG_NS}}}animate"))
    assert len(anims) > 0
    durs = set()
    linear_count = 0
    discrete_tickers = []
    path_d_anims = 0
    dashoffset_anims = 0
    parent_map = {child: parent for parent in root.iter() for child in parent}

    for anim_el in anims:
        attr_name = anim_el.attrib.get("attributeName", "")
        calc_mode = anim_el.attrib.get("calcMode", "linear")
        dur = anim_el.attrib.get("dur", "")
        rep = anim_el.attrib.get("repeatCount", "")
        vals_raw = anim_el.attrib.get("values", "")
        keys_raw = anim_el.attrib.get("keyTimes", "")
        assert attr_name in {"d", "cx", "cy", "x", "y", "opacity", "stroke-dashoffset"}
        assert calc_mode in {"linear", "discrete", "paced", "spline"}
        assert re.match(r"^\d+(\.\d+)?s$", dur)
        assert rep == "indefinite"
        durs.add(dur)

        vals = vals_raw.split(";")
        keys = [float(k) for k in keys_raw.split(";")]
        assert len(vals) == len(keys) and len(vals) >= 2
        assert abs(keys[0] - 0.0) <= 1e-9
        for k_prev, k_curr in zip(keys, keys[1:]):
            assert 0.0 <= k_prev <= k_curr <= 1.0 + 1e-9

        if calc_mode == "linear":
            linear_count += 1
            assert abs(keys[-1] - 1.0) <= 1e-9
            assert vals[0] == vals[1], f"{label}: HOLD_FIRST violated on {attr_name}"
            assert vals[-2] == vals[-1], f"{label}: HOLD_LAST violated on {attr_name}"
            if attr_name == "d":
                path_d_anims += 1
                expected_cmds = ["M"] + ["L"] * 16
                for v in vals:
                    assert re.findall(r"[MLZ]", v) == expected_cmds
            elif attr_name == "stroke-dashoffset":
                dashoffset_anims += 1
                parent = parent_map.get(anim_el)
                assert parent is not None
                total_len = float(parent.attrib["stroke-dashoffset"])
                assert parent.attrib.get("stroke-dasharray") == f"{total_len:.1f} {total_len:.1f}"
                num_vals = [float(v) for v in vals]
                assert abs(num_vals[0] - total_len) <= 1e-6 and abs(num_vals[-1]) <= 1e-6
                for a_v, b_v in zip(num_vals, num_vals[1:]):
                    assert a_v >= b_v - 1e-6
        elif calc_mode == "discrete":
            assert attr_name == "opacity"
            discrete_tickers.append(([int(v) for v in vals], keys))

    assert len(durs) == 1 and len(discrete_tickers) >= 2
    boundaries = sorted({0.0, 1.0} | {k for _, ks in discrete_tickers for k in ks})
    sample_points = []
    for b0, b1 in zip(boundaries, boundaries[1:]):
        if b1 > b0 + 1e-9:
            sample_points.extend([0.5 * (b0 + b1), b0])

    def eval_discrete(vs: list[int], ks: list[float], t: float) -> int:
        idx = 0
        for j, kj in enumerate(ks):
            if t >= kj - 1e-12:
                idx = j
            else:
                break
        return vs[idx]

    for t in sample_points:
        if t < 1.0 - 1e-9:
            assert sum(eval_discrete(vs, ks, t) for vs, ks in discrete_tickers) == 1

    return {
        "label": label,
        "duration": next(iter(durs)),
        "total_animates": len(anims),
        "linear_animates": linear_count,
        "discrete_frames": len(discrete_tickers),
        "path_d_animates": path_d_anims,
        "dashoffset_animates": dashoffset_anims,
    }


class SandboxHTMLValidator(HTMLParser):
    """Parse static HTML to verify Origin:null sandbox and strict CSP safety."""

    def __init__(self) -> None:
        super().__init__()
        self.external_scripts: list[str] = []
        self.external_stylesheets: list[str] = []
        self.forbidden_embeds: list[str] = []
        self.svg_data_uris: list[str] = []
        self.inline_scripts: list[str] = []
        self.inline_styles: list[str] = []
        self.has_data_theme = False
        self._in_script = False
        self._in_style = False
        self._buf: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        attr_dict = {k.lower(): (v or "") for k, v in attrs}
        t = tag.lower()
        if t == "html" and "data-theme" in attr_dict:
            self.has_data_theme = True
        elif t == "script":
            src = attr_dict.get("src", "").strip()
            if src:
                self.external_scripts.append(src)
            else:
                self._in_script = True
                self._buf = []
        elif t == "style":
            self._in_style = True
            self._buf = []
        elif t == "link":
            rel = attr_dict.get("rel", "").lower()
            href = attr_dict.get("href", "").strip()
            if "stylesheet" in rel or "font" in rel or href.startswith("http"):
                self.external_stylesheets.append(href)
        elif t in {"object", "embed", "iframe"}:
            self.forbidden_embeds.append(f"<{t}>")
        elif t == "img":
            src = attr_dict.get("src", "")
            if src.startswith("data:image/svg+xml;base64,"):
                self.svg_data_uris.append(src)

    def handle_endtag(self, tag: str) -> None:
        t = tag.lower()
        if t == "script" and self._in_script:
            self._in_script = False
            self.inline_scripts.append("".join(self._buf))
            self._buf = []
        elif t == "style" and self._in_style:
            self._in_style = False
            self.inline_styles.append("".join(self._buf))
            self._buf = []

    def handle_data(self, data: str) -> None:
        if self._in_script or self._in_style:
            self._buf.append(data)


def verify_html_bundle_invariants(html_text: str, label: str) -> dict:
    """Verify HTML bundle immunity to Origin:null and strict CSP restrictions."""
    parser = SandboxHTMLValidator()
    parser.feed(html_text)
    assert parser.has_data_theme
    assert not parser.external_scripts and not parser.external_stylesheets and not parser.forbidden_embeds
    for css in parser.inline_styles:
        assert "@import" not in css.lower() and "http://" not in css.lower() and "https://" not in css.lower()
    assert len(parser.inline_scripts) >= 1
    for js in parser.inline_scripts:
        assert "fetch(" not in js and "XMLHttpRequest" not in js
        ls_matches = list(re.finditer(r"localStorage", js))
        try_bodies: list[str] = []
        for tm in re.finditer(r"\btry\s*\{", js):
            depth, pos_i = 1, tm.end()
            while pos_i < len(js) and depth > 0:
                depth += (1 if js[pos_i] == "{" else (-1 if js[pos_i] == "}" else 0))
                pos_i += 1
            if re.match(r"\s*catch\s*\([^)]*\)\s*\{", js[pos_i:]):
                try_bodies.append(js[tm.end() : pos_i - 1])
        assert ls_matches and sum(b.count("localStorage") for b in try_bodies) == len(ls_matches)

    decoded_svgs = []
    for idx, uri in enumerate(parser.svg_data_uris):
        b64_payload = uri[len("data:image/svg+xml;base64,") :]
        assert re.fullmatch(r"[A-Za-z0-9+/=]+", b64_payload)
        svg_str = base64.b64decode(b64_payload, validate=True).decode("utf-8")
        decoded_svgs.append((len(svg_str.encode("utf-8")), len(b64_payload), verify_smil_svg_invariants(svg_str, f"{label}:svg[{idx+1}]")))
    return {
        "label": label,
        "html_bytes": len(html_text.encode("utf-8")),
        "embedded_svg_count": len(decoded_svgs),
        "raw_svg_bytes": sum(x[0] for x in decoded_svgs),
        "base64_svg_bytes": sum(x[1] for x in decoded_svgs),
    }


def verify_harmonic_vs_linear_pareto_geometry() -> dict:
    """Verify closed-form AM-GM-HM bounds, convexity, and Silesia Pareto inversions."""
    max_formula_discrepancy = 0.0
    max_rho_seg = None

    for series_name, pts in EMBEDDED_SERIES.items():
        for a, b in zip(pts, pts[1:]):
            la, _r0, v0, _ = a
            lb, _r1, v1, _ = b
            rho = max(v0, v1) / min(v0, v1)
            rel_lin_theory = ((rho - 1.0) ** 2) / (4.0 * rho)
            abs_lin_theory = (math.sqrt(v0) - math.sqrt(v1)) ** 2
            rel_log_theory = ((math.sqrt(rho) - 1.0) ** 2) / (2.0 * math.sqrt(rho))
            f_abs_star = math.sqrt(v1) / (math.sqrt(v0) + math.sqrt(v1))

            vh_half = 1.0 / (0.5 / v0 + 0.5 / v1)
            vlin_half = 0.5 * v0 + 0.5 * v1
            vlog_half = math.sqrt(v0 * v1)
            vh_star = 1.0 / ((1.0 - f_abs_star) / v0 + f_abs_star / v1)
            vlin_star = (1.0 - f_abs_star) * v0 + f_abs_star * v1

            disc = max(
                abs(rel_lin_theory - ((vlin_half / vh_half) - 1.0)),
                abs(rel_log_theory - ((vlog_half / vh_half) - 1.0)),
                abs(abs_lin_theory - (vlin_star - vh_star)),
            )
            max_formula_discrepancy = max(max_formula_discrepancy, disc)
            assert disc < 1e-11
            if max_rho_seg is None or rho > max_rho_seg["rho"]:
                max_rho_seg = {
                    "segment": f"{series_name} L{la}->L{lb}",
                    "rho": round(rho, 4),
                    "rel_lin_pct": round(rel_lin_theory * 100.0, 2),
                    "rel_log_pct": round(rel_log_theory * 100.0, 2),
                    "abs_lin_mibs": round(abs_lin_theory, 2),
                }
            for k in range(1, 64):
                f = k / 64.0
                vh = 1.0 / ((1.0 - f) / v0 + f / v1)
                vlog = (v0 ** (1.0 - f)) * (v1 ** f)
                vlin = (1.0 - f) * v0 + f * v1
                if abs(v0 - v1) > 1e-9:
                    assert vh < vlog < vlin

    def check_inversion(subj_key: str, subj_lvl: int, ref_key: str, ref_la: int, ref_lb: int) -> dict:
        _, rm, vm, _ = next(x for x in EMBEDDED_SERIES[subj_key] if x[0] == subj_lvl)
        _, r0, v0, _ = next(x for x in EMBEDDED_SERIES[ref_key] if x[0] == ref_la)
        _, r1, v1, _ = next(x for x in EMBEDDED_SERIES[ref_key] if x[0] == ref_lb)
        f = (rm - r0) / (r1 - r0)
        assert 0.0 < f < 1.0
        vh = 1.0 / ((1.0 - f) / v0 + f / v1)
        vlog = (v0 ** (1.0 - f)) * (v1 ** f)
        vlin = (1.0 - f) * v0 + f * v1
        assert vh < vm < vlin
        return {
            "subject": f"{subj_key} L{subj_lvl}",
            "reference_chord": f"{ref_key} L{ref_la}->L{ref_lb}",
            "ratio": round(rm, 6),
            "v_subject": vm,
            "v_harm_ref": round(vh, 2),
            "v_log_ref": round(vlog, 2),
            "v_lin_ref": round(vlin, 2),
            "true_gain_vs_harm_pct": round((vm / vh - 1.0) * 100.0, 2),
            "false_loss_vs_lin_pct": round((vm / vlin - 1.0) * 100.0, 2),
            "also_inverted_by_semilog_line": vm < vlog,
        }

    inversions = [
        check_inversion("lean_zip_2f7a63f", 5, "miniz_oxide_0_9_1", 5, 6),
        check_inversion("rust_safe_hash4_bt", 2, "rust_unsafe_bt_dp_simd", 1, 2),
        check_inversion("rust_unsafe_bt_dp_simd", 7, "rust_safe_hash4_bt", 8, 9),
        check_inversion("rust_unsafe_row_hash_simd", 8, "rust_safe_hash4_bt", 8, 9),
        check_inversion("miniz_oxide_0_9_1", 8, "zlib_1_3_2", 7, 8),
    ]
    assert inversions[0]["also_inverted_by_semilog_line"] is True
    assert inversions[1]["also_inverted_by_semilog_line"] is True

    pixel_errors = {}
    for label, v0, v1 in [
        ("lean_zip_2f7a63f L8->L9", 18.36, 2.55),
        ("rust_safe_hash4_bt L8->L9", 24.28, 7.42),
        ("rust_unsafe_bt_dp_simd L1->L2", 220.24, 129.40),
    ]:
        max_px_n1, max_px_n16 = 0.0, 0.0
        for m in range(1600):
            f = m / 1600.0
            y_exact = sy(1.0 / ((1.0 - f) / v0 + f / v1))
            y_n1 = (1.0 - f) * sy(v0) + f * sy(v1)
            max_px_n1 = max(max_px_n1, abs(y_exact - y_n1))
            i0 = min(int(f * 16), 15)
            f0, f1 = i0 / 16.0, (i0 + 1) / 16.0
            alpha = (f - f0) / (f1 - f0)
            y_n16 = (1.0 - alpha) * sy(1.0 / ((1.0 - f0) / v0 + f0 / v1)) + alpha * sy(
                1.0 / ((1.0 - f1) / v0 + f1 / v1)
            )
            max_px_n16 = max(max_px_n16, abs(y_exact - y_n16))
        assert max_px_n1 > 30.0 * max_px_n16
        pixel_errors[label] = {
            "n1_px": round(max_px_n1, 2),
            "n16_px": round(max_px_n16, 4),
            "reduction_factor": round(max_px_n1 / max_px_n16, 1),
        }

    return {
        "max_formula_discrepancy": max_formula_discrepancy,
        "max_rho_segment": max_rho_seg,
        "inversions_verified": inversions,
        "pixel_errors": pixel_errors,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--html", type=Path, default=None, help="Optional HTML bundle path to audit")
    ap.add_argument("--svg", type=Path, default=None, help="Optional SMIL SVG path to audit")
    args = ap.parse_args()

    synth_frames = [
        {"tag": "base", "label": "Upstream miniz_oxide 0.9.1", "points": [(lv, r, c) for lv, r, c, _ in EMBEDDED_SERIES["miniz_oxide_0_9_1"]]},
        {"tag": "lean", "label": "Lean 4 lean_zip_2f7a63f", "points": [(lv, r, c) for lv, r, c, _ in EMBEDDED_SERIES["lean_zip_2f7a63f"]]},
        {"tag": "safe", "label": "Safe Rust hash4 + BT/DP", "points": [(lv, r, c) for lv, r, c, _ in EMBEDDED_SERIES["rust_safe_hash4_bt"]]},
    ]
    synth_svg = synthesize_smil_svg(synth_frames)
    synth_svg_stats = verify_smil_svg_invariants(synth_svg, "synthesized_svg")
    synth_b64 = base64.b64encode(synth_svg.encode("utf-8")).decode("ascii")
    synth_html = (
        '<!DOCTYPE html><html lang="en" data-theme="light"><head><meta charset="utf-8"/>'
        '<style>:root { --bg: #fff; }</style></head><body>'
        f'<img src="data:image/svg+xml;base64,{synth_b64}" class="zoomable-svg" alt="probe"/>'
        '<script>(function(){try{window.localStorage.setItem("k","v");}catch(_){}'
        'try{var x=window.localStorage.getItem("k");}catch(_){}})();</script></body></html>'
    )
    synth_html_stats = verify_html_bundle_invariants(synth_html, "synthesized_html")
    math_stats = verify_harmonic_vs_linear_pareto_geometry()

    out: dict = {
        "status": "PASS",
        "synthesized_smil_svg": synth_svg_stats,
        "synthesized_html_bundle": synth_html_stats,
        "harmonic_vs_linear_geometry": math_stats,
    }
    if args.svg and args.svg.is_file():
        out["extra_svg_audit"] = verify_smil_svg_invariants(args.svg.read_text(encoding="utf-8"), args.svg.name)
    if args.html and args.html.is_file():
        out["extra_html_audit"] = verify_html_bundle_invariants(args.html.read_text(encoding="utf-8"), args.html.name)
    print(json.dumps(out, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
