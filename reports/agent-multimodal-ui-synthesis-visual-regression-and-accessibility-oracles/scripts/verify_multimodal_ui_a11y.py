#!/usr/bin/env python3
"""Deterministic verification probes for multimodal UI synthesis, visual-regression
diffing, and automated web accessibility oracles.

Pure Python 3.10+ standard library only. Deterministic across PYTHONHASHSEED.
Zero disk writes and zero network calls.
"""

from __future__ import annotations

from dataclasses import dataclass
from difflib import SequenceMatcher
from itertools import permutations
import math
import random
from typing import Dict, List, Sequence, Tuple


# ============================================================================
# Shared Exact Algorithms (Hungarian Assignment, CIEDE2000, WCAG Luminance)
# ============================================================================


def linear_sum_assignment(cost_matrix: Sequence[Sequence[float]]) -> List[Tuple[int, int]]:
    """Exact Kuhn-Munkres (Hungarian) minimum-weight assignment for rectangular matrices.

    Returns sorted list of (row_idx, col_idx) pairs of length min(n_rows, n_cols),
    matching scipy.optimize.linear_sum_assignment semantics deterministically.
    """
    n_rows = len(cost_matrix)
    if n_rows == 0:
        return []
    n_cols = len(cost_matrix[0])
    if n_cols == 0:
        return []

    transposed = False
    if n_rows > n_cols:
        mat = [[cost_matrix[r][c] for r in range(n_rows)] for c in range(n_cols)]
        n_rows, n_cols = n_cols, n_rows
        transposed = True
    else:
        mat = [list(row) for row in cost_matrix]

    # 1-indexed standard O(n^2 * m) potential-based Hungarian algorithm
    u = [0.0] * (n_rows + 1)
    v = [0.0] * (n_cols + 1)
    p = [0] * (n_cols + 1)
    way = [0] * (n_cols + 1)

    for i in range(1, n_rows + 1):
        p[0] = i
        j0 = 0
        minv = [math.inf] * (n_cols + 1)
        used = [False] * (n_cols + 1)
        while True:
            used[j0] = True
            i0 = p[j0]
            delta = math.inf
            j1 = 0
            row_i0 = mat[i0 - 1]
            for j in range(1, n_cols + 1):
                if not used[j]:
                    cur = row_i0[j - 1] - u[i0] - v[j]
                    if cur < minv[j]:
                        minv[j] = cur
                        way[j] = j0
                    if minv[j] < delta:
                        delta = minv[j]
                        j1 = j
            for j in range(n_cols + 1):
                if used[j]:
                    u[p[j]] += delta
                    v[j] -= delta
                else:
                    minv[j] -= delta
            j0 = j1
            if p[j0] == 0:
                break
        while True:
            j1 = way[j0]
            p[j0] = p[j1]
            j0 = j1
            if j0 == 0:
                break

    pairs: List[Tuple[int, int]] = []
    for j in range(1, n_cols + 1):
        if p[j] != 0:
            r_idx = p[j] - 1
            c_idx = j - 1
            pairs.append((c_idx, r_idx) if transposed else (r_idx, c_idx))
    pairs.sort()
    return pairs


def srgb_to_lab(rgb: Tuple[int, int, int]) -> Tuple[float, float, float]:
    """Convert 8-bit sRGB (0..255) to CIE L*a*b* directly in D65 illuminant."""
    def lin(c: int) -> float:
        x = c / 255.0
        return x / 12.92 if x <= 0.04045 else ((x + 0.055) / 1.055) ** 2.4

    r, g, b = lin(rgb[0]), lin(rgb[1]), lin(rgb[2])
    # sRGB to XYZ (D65)
    x = 0.4124564 * r + 0.3575761 * g + 0.1804375 * b
    y = 0.2126729 * r + 0.7151522 * g + 0.0721750 * b
    z = 0.0193339 * r + 0.1191920 * g + 0.9503041 * b

    # Normalize by D65 reference white
    xn, yn, zn = 0.95047, 1.00000, 1.08883
    eps = 216.0 / 24389.0
    kappa = 24389.0 / 27.0

    def f(t: float) -> float:
        return t ** (1.0 / 3.0) if t > eps else (kappa * t + 16.0) / 116.0

    fx, fy, fz = f(x / xn), f(y / yn), f(z / zn)
    L = 116.0 * fy - 16.0
    a = 500.0 * (fx - fy)
    b_star = 200.0 * (fy - fz)
    return (L, a, b_star)


def ciede2000(lab1: Tuple[float, float, float], lab2: Tuple[float, float, float]) -> float:
    """Exact CIEDE2000 color difference (Sharma, Wu, Dalal 2005; kL=kC=kH=1)."""
    L1, a1, b1 = lab1
    L2, a2, b2 = lab2

    C1 = math.hypot(a1, b1)
    C2 = math.hypot(a2, b2)
    C_bar = 0.5 * (C1 + C2)
    C_bar7 = C_bar ** 7
    G = 0.5 * (1.0 - math.sqrt(C_bar7 / (C_bar7 + 25.0 ** 7)))

    a1p = (1.0 + G) * a1
    a2p = (1.0 + G) * a2
    C1p = math.hypot(a1p, b1)
    C2p = math.hypot(a2p, b2)

    def hp(ap: float, bp: float) -> float:
        if ap == 0.0 and bp == 0.0:
            return 0.0
        deg = math.degrees(math.atan2(bp, ap))
        return deg + 360.0 if deg < 0.0 else deg

    h1p = hp(a1p, b1)
    h2p = hp(a2p, b2)

    dLp = L2 - L1
    dCp = C2p - C1p

    if C1p * C2p == 0.0:
        dhp = 0.0
    else:
        diff = h2p - h1p
        if abs(diff) <= 180.0:
            dhp = diff
        elif diff > 180.0:
            dhp = diff - 360.0
        else:
            dhp = diff + 360.0

    dHp = 2.0 * math.sqrt(C1p * C2p) * math.sin(math.radians(dhp / 2.0))

    L_barp = 0.5 * (L1 + L2)
    C_barp = 0.5 * (C1p + C2p)

    if C1p * C2p == 0.0:
        h_barp = h1p + h2p
    elif abs(h1p - h2p) <= 180.0:
        h_barp = 0.5 * (h1p + h2p)
    elif h1p + h2p < 360.0:
        h_barp = 0.5 * (h1p + h2p + 360.0)
    else:
        h_barp = 0.5 * (h1p + h2p - 360.0)

    T = (
        1.0
        - 0.17 * math.cos(math.radians(h_barp - 30.0))
        + 0.24 * math.cos(math.radians(2.0 * h_barp))
        + 0.32 * math.cos(math.radians(3.0 * h_barp + 6.0))
        - 0.20 * math.cos(math.radians(4.0 * h_barp - 63.0))
    )

    d_theta = 30.0 * math.exp(-(((h_barp - 275.0) / 25.0) ** 2))
    C_barp7 = C_barp ** 7
    R_C = 2.0 * math.sqrt(C_barp7 / (C_barp7 + 25.0 ** 7))
    L_term = (L_barp - 50.0) ** 2
    S_L = 1.0 + (0.015 * L_term) / math.sqrt(20.0 + L_term)
    S_C = 1.0 + 0.045 * C_barp
    S_H = 1.0 + 0.015 * C_barp * T
    R_T = -math.sin(math.radians(2.0 * d_theta)) * R_C

    return math.sqrt(
        (dLp / S_L) ** 2
        + (dCp / S_C) ** 2
        + (dHp / S_H) ** 2
        + R_T * (dCp / S_C) * (dHp / S_H)
    )


# Self-check Sharma et al. (2005) Test Pair 1
_SHARMA_PAIR1_DE00 = ciede2000((50.0, 2.6772, -79.7751), (50.0, 0.0, -82.7485))
assert abs(_SHARMA_PAIR1_DE00 - 2.0425) < 1e-4, f"CIEDE2000 check failed: {_SHARMA_PAIR1_DE00}"


# ============================================================================
# PROBE 1: Design2Code Evaluator Forensics (NoviScl/Design2Code@7a575e4c)
# ============================================================================


D2C_TEXT_TAGS = (
    "p", "h1", "h2", "h3", "h4", "h5", "h6",
    "div", "span", "a", "b", "li", "table", "td", "th",
    "button", "footer", "header", "figcaption",
)


def d2c_calculate_similarity(block1: dict, block2: dict, max_distance: float = 1.42) -> float:
    """Exact port of visual_score.py:36-38 (max_distance parameter is ignored)."""
    del max_distance
    return SequenceMatcher(None, block1["text"], block2["text"]).ratio()


def d2c_adjust_cost_for_context(
    cost_matrix: List[List[float]], consecutive_bonus: float = 0.1, window_size: int = 1
) -> List[List[float]]:
    """Exact port of visual_score.py:41-61."""
    if window_size <= 0:
        return [row[:] for row in cost_matrix]
    n = len(cost_matrix)
    m = len(cost_matrix[0]) if n else 0
    adjusted = [row[:] for row in cost_matrix]
    for i in range(n):
        for j in range(m):
            if adjusted[i][j] >= -0.5:
                continue
            r0, r1 = max(0, i - window_size), min(n, i + window_size + 1)
            c0, c1 = max(0, j - window_size), min(m, j + window_size + 1)
            flattened = [cost_matrix[r][c] for r in range(r0, r1) for c in range(c0, c1)]
            sorted_arr = sorted(flattened, reverse=True)
            # Remove one occurrence of cost_matrix[i][j]
            sorted_arr.remove(cost_matrix[i][j])
            top_k = sorted_arr[-window_size * 2 :]
            adjusted[i][j] += consecutive_bonus * sum(top_k)
    return adjusted


def d2c_evaluate_blocks(
    predict_blocks: List[dict],
    original_blocks: List[dict],
    consecutive_bonus: float = 0.1,
    window_size: int = 1,
) -> Dict[str, float]:
    """Exact port of the core matching/scoring loop (visual_score.py:453-561) on
    pre-merged non-coalescing blocks.

    Omits merge_blocks_by_bbox / find_possible_merge (lines 450, 473-474) and
    computes CIE Lab directly in D65 rather than colormath's D65->D50 Bradford
    adaptation; outputs match upstream identically on Probe 1's distinct-bbox,
    exact-text, identical-color fixtures.
    """
    if not predict_blocks or not original_blocks:
        return {"block": 0.0, "text": 0.0, "position": 0.0, "color": 0.0, "matched_count": 0}

    cost = [
        [-d2c_calculate_similarity(pb, ob) for ob in original_blocks]
        for pb in predict_blocks
    ]
    adj_cost = d2c_adjust_cost_for_context(cost, consecutive_bonus, window_size)
    matching = linear_sum_assignment(adj_cost)

    filtered = []
    for i, j in matching:
        ts = SequenceMatcher(None, predict_blocks[i]["text"], original_blocks[j]["text"]).ratio()
        if ts < 0.5:
            continue
        filtered.append((i, j, ts))

    if not filtered:
        return {"block": 0.0, "text": 0.0, "position": 0.0, "color": 0.0, "matched_count": 0}

    idx1 = {i for i, _, _ in filtered}
    idx2 = {j for _, j, _ in filtered}
    unmatched_1 = sum(
        pb["bbox"][2] * pb["bbox"][3]
        for i, pb in enumerate(predict_blocks)
        if i not in idx1
    )
    unmatched_2 = sum(
        ob["bbox"][2] * ob["bbox"][3]
        for j, ob in enumerate(original_blocks)
        if j not in idx2
    )
    sum_areas = [unmatched_1 + unmatched_2]
    matched_areas = []
    text_scores = []
    pos_scores = []
    color_scores = []

    for i, j, ts in filtered:
        pb = predict_blocks[i]
        ob = original_blocks[j]
        area = pb["bbox"][2] * pb["bbox"][3] + ob["bbox"][2] * ob["bbox"][3]
        # visual_score.py:509-512 center-only Chebyshev distance
        cx1, cy1 = pb["bbox"][0] + pb["bbox"][2] / 2.0, pb["bbox"][1] + pb["bbox"][3] / 2.0
        cx2, cy2 = ob["bbox"][0] + ob["bbox"][2] / 2.0, ob["bbox"][1] + ob["bbox"][3] / 2.0
        pos_sim = 1.0 - max(abs(cx2 - cx1), abs(cy2 - cy1))
        # visual_score.py:142 CIEDE2000 normalized similarity
        de00 = ciede2000(srgb_to_lab(pb["color"]), srgb_to_lab(ob["color"]))
        col_sim = max(0.0, 1.0 - de00 / 100.0)
        # visual_score.py:520 trivial positive ratio check
        ratio_w = max(pb["bbox"][2], ob["bbox"][2]) / min(pb["bbox"][2], ob["bbox"][2])
        ratio_h = max(pb["bbox"][3], ob["bbox"][3]) / min(pb["bbox"][3], ob["bbox"][3])
        assert ratio_w > 0.0 and ratio_h > 0.0

        sum_areas.append(area)
        matched_areas.append(area)
        text_scores.append(ts)
        pos_scores.append(pos_sim)
        color_scores.append(col_sim)

    return {
        "block": sum(matched_areas) / sum(sum_areas),
        "text": sum(text_scores) / len(text_scores),
        "position": sum(pos_scores) / len(pos_scores),
        "color": sum(color_scores) / len(color_scores),
        "matched_count": len(filtered),
    }


def dom_bbox_oracle(blocks: List[dict]) -> Dict[str, float]:
    """Structured normalized DOM bounding-box overlap and viewport clipping oracle."""
    clip_violations = 0
    max_overflow = 0.0
    for b in blocks:
        x, y, w, h = b["bbox"]
        ov = max(0.0, -x, -y, x + w - 1.0, y + h - 1.0)
        if ov > 1e-9:
            clip_violations += 1
            max_overflow = max(max_overflow, ov)

    overlap_pairs = 0
    max_iou = 0.0
    for i in range(len(blocks)):
        x1, y1, w1, h1 = blocks[i]["bbox"]
        for j in range(i + 1, len(blocks)):
            x2, y2, w2, h2 = blocks[j]["bbox"]
            ix = max(0.0, min(x1 + w1, x2 + w2) - max(x1, x2))
            iy = max(0.0, min(y1 + h1, y2 + h2) - max(y1, y2))
            inter = ix * iy
            if inter > 1e-9:
                overlap_pairs += 1
                union = w1 * h1 + w2 * h2 - inter
                max_iou = max(max_iou, inter / union if union > 0 else 0.0)

    return {
        "clip_violations": clip_violations,
        "max_overflow": max_overflow,
        "overlap_pairs": overlap_pairs,
        "max_iou": max_iou,
    }


def run_probe_1() -> None:
    print("========================================================================")
    print("PROBE 1: Design2Code Evaluator Forensics (NoviScl/Design2Code@7a575e4c)")
    print("Provenance: [exact port of core visual_score/ocr_free_utils logic] + [controlled simulation]")
    print("========================================================================")

    # 1A. Verify 19-tag whitelist omissions & exact uint8 +/-4 wraparound domain
    # (ocr_free_utils.py:14-25, 49-53, 60-64, 94, 124, 212-213, 235-259)
    assert len(D2C_TEXT_TAGS) == 19
    omitted_semantic_tags = ("label", "input", "nav", "section", "article", "main", "strong", "option")
    for tag in omitted_semantic_tags:
        assert tag not in D2C_TEXT_TAGS
    # Design2Code Table 5 exact benchmark frequencies of 6 omitted tags
    table5_omitted_counts = {
        "option": 1194, "input": 995, "strong": 595,
        "nav": 416, "section": 381, "label": 339,
    }
    total_table5_omitted = sum(table5_omitted_counts.values())
    assert total_table5_omitted == 3920

    # Exact uint8 wraparound in ocr_free_utils.py:212-213 (`lower = color - 4; upper = color + 4`)
    def uint8_inrange_empty(channel_val: int) -> Tuple[int, int, bool]:
        lower = (channel_val - 4) & 0xFF
        upper = (channel_val + 4) & 0xFF
        # OpenCV cv2.inRange returns empty when lower > upper
        return lower, upper, lower > upper

    # ColorPool(offset=0) (used for p_html/p_png passed to get_blocks_from_image_diff_pixels at L237,250,252)
    # generates channels in range(10, 251, 16) = [10, 26, ..., 250]: ZERO channels trigger uint8 +/-4 wraparound.
    # (ColorPool(offset=50) at L238 is used ONLY by find_different_pixels at L243 with Python-int mod-256 arithmetic.)
    pool0_channels = list(range(10, 251, 16))
    assert len(pool0_channels) == 16 and pool0_channels[0] == 10 and pool0_channels[-1] == 250
    pool0_wrapped = [c for c in pool0_channels if uint8_inrange_empty(c)[2]]
    assert len(pool0_wrapped) == 0

    # Latent uint8 +/-4 wraparound triggers specifically for c < 4 or c > 251 passed to cv2.inRange,
    # such as default parent_color='#000000' (L124) or inline '#ffffff' (L212-213).
    wrapped_domain = [c for c in range(256) if uint8_inrange_empty(c)[2]]
    assert wrapped_domain == [0, 1, 2, 3, 252, 253, 254, 255]
    low0, up0, empty0 = uint8_inrange_empty(0)      # default parent_color='#000000' (line 124)
    low3, up3, empty3 = uint8_inrange_empty(3)
    low252, up252, empty252 = uint8_inrange_empty(252)
    low255, up255, empty255 = uint8_inrange_empty(255)  # inline '#ffffff'
    assert empty0 and low0 == 252 and up0 == 4
    assert empty3 and low3 == 255 and up3 == 7
    assert empty252 and low252 == 248 and up252 == 0
    assert empty255 and low255 == 251 and up255 == 3

    # 1B. Case A: Coincident-center 3.0x width / 4.0x height overlap + viewport clipping
    ref_blocks = [
        {"tag": "h1", "text": "quarterly revenue report", "bbox": (0.30, 0.20, 0.40, 0.10), "color": (20, 20, 20)},
        {"tag": "p",  "text": "net margin increased 4.2%", "bbox": (0.30, 0.40, 0.40, 0.10), "color": (40, 40, 40)},
    ]
    # Inflate block 0 around exact center (0.50, 0.25) to width=1.20 (3.0x), height=0.40 (4.0x)
    # -> x=-0.10..1.10, y=0.05..0.45 (clips viewport by 0.10 and overlaps block 1)
    broken_overlap_clip = [
        {"tag": "h1", "text": "quarterly revenue report", "bbox": (-0.10, 0.05, 1.20, 0.40), "color": (20, 20, 20)},
        {"tag": "p",  "text": "net margin increased 4.2%", "bbox": (0.30, 0.40, 0.40, 0.10), "color": (40, 40, 40)},
    ]
    sc_case_a = d2c_evaluate_blocks(broken_overlap_clip, ref_blocks)
    ora_ref = dom_bbox_oracle(ref_blocks)
    ora_case_a = dom_bbox_oracle(broken_overlap_clip)
    assert ora_ref["clip_violations"] == 0 and ora_ref["overlap_pairs"] == 0
    assert sc_case_a["block"] == 1.0 and sc_case_a["text"] == 1.0
    assert abs(sc_case_a["position"] - 1.0) < 1e-12 and abs(sc_case_a["color"] - 1.0) < 1e-12
    assert ora_case_a["clip_violations"] == 1 and ora_case_a["overlap_pairs"] == 1

    # 1C. Case B: Deleted top-level <nav>/<label> (no whitelisted ancestor) & <input value=...> attribute text
    # Note (ocr_free_utils.py:49-53, 124-134): unwhitelisted tags nested under a whitelisted text_tags ancestor
    # inherit parent_color, whereas top-level <nav>/<label> under <body>/<form> (unshifted) and <input value=...>
    # / unexpanded <option> are omitted from extraction.
    ref_full_dom = [
        {"tag": "header", "text": "account settings", "bbox": (0.10, 0.05, 0.80, 0.08), "color": (15, 15, 15), "has_whitelisted_ancestor": False},
        {"tag": "nav",    "text": "home billing security", "bbox": (0.10, 0.15, 0.80, 0.06), "color": (30, 30, 30), "has_whitelisted_ancestor": False},
        {"tag": "label",  "text": "email address", "bbox": (0.10, 0.28, 0.30, 0.05), "color": (30, 30, 30), "has_whitelisted_ancestor": False},
        {"tag": "input",  "text": "user@example.com", "bbox": (0.42, 0.28, 0.40, 0.05), "color": (30, 30, 30), "has_whitelisted_ancestor": True},
        {"tag": "p",      "text": "manage notifications below", "bbox": (0.10, 0.42, 0.80, 0.08), "color": (60, 60, 60), "has_whitelisted_ancestor": False},
    ]
    # Candidate deletes <nav>, <label>, <input> completely
    cand_deleted_dom = [b for b in ref_full_dom if b["tag"] in ("header", "p")]

    def d2c_extract_visible(nodes: List[dict]) -> List[dict]:
        # Mirrors ocr_free_utils.py:49-53, 124-134: <input> holds value attribute (not text node);
        # other non-whitelisted tags only shift color when inheriting from a whitelisted ancestor.
        out = []
        for b in nodes:
            if b["tag"] == "input":
                continue
            if b["tag"] in D2C_TEXT_TAGS or b["has_whitelisted_ancestor"]:
                out.append(b)
        return out

    ref_extracted = d2c_extract_visible(ref_full_dom)
    cand_extracted = d2c_extract_visible(cand_deleted_dom)
    sc_case_b = d2c_evaluate_blocks(cand_extracted, ref_extracted)
    assert len(ref_extracted) == 2 and len(cand_extracted) == 2
    assert sc_case_b["block"] == 1.0 and sc_case_b["text"] == 1.0 and sc_case_b["position"] == 1.0
    missing_semantic = len(ref_full_dom) - len(cand_deleted_dom)
    assert missing_semantic == 3

    # 1D. Case C: Position-blind Hungarian assignment on duplicate button labels ("buy")
    # Visually identical rendered page whose DOM extraction order reverses two "buy" cards
    ref_dup = [
        {"tag": "p",      "text": "starter plan", "bbox": (0.10, 0.10, 0.20, 0.05), "color": (10, 10, 10)},
        {"tag": "button", "text": "buy",          "bbox": (0.10, 0.20, 0.10, 0.05), "color": (255, 255, 255)},
        {"tag": "button", "text": "buy",          "bbox": (0.70, 0.80, 0.10, 0.05), "color": (255, 255, 255)},
        {"tag": "p",      "text": "enterprise",   "bbox": (0.70, 0.70, 0.20, 0.05), "color": (10, 10, 10)},
    ]
    # Swap only the two "buy" entries in DOM order (exact same 2D pixels on screen!)
    cand_dup_reordered = [ref_dup[0], ref_dup[2], ref_dup[1], ref_dup[3]]
    sc_case_c = d2c_evaluate_blocks(cand_dup_reordered, ref_dup)
    # Because context window ties index 1 to "starter plan" (index 0) and index 2 to "enterprise" (index 3),
    # Design2Code pairs (0.70,0.80) with (0.10,0.20), giving position penalty 0.60 on both buttons -> avg 0.70!
    assert abs(sc_case_c["position"] - 0.70) < 1e-9

    # 1E. Case D: Tall-page aspect-ratio squash bug (visual_score.py:360-369)
    w_tall, h_tall = 1280, 4800
    squashed = (w_tall, w_tall) if w_tall < h_tall else (h_tall, h_tall)
    distortion_factor = (h_tall / w_tall) / (squashed[1] / squashed[0])
    assert squashed == (1280, 1280) and abs(distortion_factor - 3.75) < 1e-12

    print(f"  Whitelist size: {len(D2C_TEXT_TAGS)} tags | Table-5 omitted semantic tags sum: {total_table5_omitted} instances")
    print(
        f"  uint8 +/-4 wraparound (L212-213): ColorPool(0) [10..250] wrapped={len(pool0_wrapped)}/16 (safe); "
        f"latent wrap domain c in {{0..3,252..255}}: c=0 (parent_color='#000000') -> [{low0},{up0}] empty={empty0}; "
        f"c=255 ('#ffffff') -> [{low255},{up255}] empty={empty255}"
    )
    print(f"  Case A (3.0x width / 4.0x height overlap + viewport clip, same center): D2C Block={sc_case_a['block']:.4f} Text={sc_case_a['text']:.4f} Pos={sc_case_a['position']:.4f} Color={sc_case_a['color']:.4f}")
    print(f"    -> DOM bbox oracle: clip_violations={ora_case_a['clip_violations']}, max_overflow={ora_case_a['max_overflow']:.2f}, overlap_pairs={ora_case_a['overlap_pairs']}, max_IoU={ora_case_a['max_iou']:.4f}")
    print(f"  Case B (deleted top-level <nav>/<label> & <input value=...>): D2C Block={sc_case_b['block']:.4f} Text={sc_case_b['text']:.4f} Pos={sc_case_b['position']:.4f} | DOM oracle missing_elements={missing_semantic}")
    print(f"  Case C (pixel-identical page, swapped DOM order of 2 'buy' buttons): D2C Pos={sc_case_c['position']:.4f} (false -0.3000 penalty)")
    print(f"  Case D (rescale_and_mask tall page 1280x4800): resized={squashed[0]}x{squashed[1]}, vertical_squash={distortion_factor:.2f}x")


# ============================================================================
# PROBE 2: ChartMimic & Plot2Code Evaluator Forensics
# ============================================================================


class ChartTypeEvaluatorBuggy:
    """Exact port of ChartMimic/ChartMimic@92ba5b97 chart_type_evaluator.py:16-100."""

    def __init__(self) -> None:
        self.metrics = {"precision": 0.0, "recall": 0.0, "f1": 0.0}

    def evaluate(self, gen_types: Dict[str, int], gold_types: Dict[str, int]) -> Dict[str, float]:
        # chart_type_evaluator.py:84-85: returns early WITHOUT resetting self.metrics!
        if len(gen_types) == 0:
            return dict(self.metrics)
        n_correct = sum(min(cnt, gold_types.get(k, 0)) for k, cnt in gen_types.items())
        total_gen = sum(gen_types.values())
        total_gold = sum(gold_types.values())
        self.metrics["precision"] = n_correct / total_gen
        self.metrics["recall"] = n_correct / total_gold
        denom = self.metrics["precision"] + self.metrics["recall"]
        self.metrics["f1"] = 0.0 if denom == 0.0 else 2.0 * self.metrics["precision"] * self.metrics["recall"] / denom
        return dict(self.metrics)


class ChartTypeEvaluatorFixed(ChartTypeEvaluatorBuggy):
    """Fixed evaluator resetting metrics on empty/crashed generation."""

    def evaluate(self, gen_types: Dict[str, int], gold_types: Dict[str, int]) -> Dict[str, float]:
        if len(gen_types) == 0:
            self.metrics = {"precision": 0.0, "recall": 0.0, "f1": 0.0}
            return dict(self.metrics)
        return super().evaluate(gen_types, gold_types)


def chartmimic_text_injector(code: str, output_file: str) -> Tuple[int, str]:
    """Exact port of ChartMimic text_evaluator.py:48-56 & 165-178."""
    # Pinned text_evaluator.py:166-170 appends a hardcoded triple-quoted suffix ending with '\n'
    # BEFORE searching for "plt.savefig".
    suffix = f"\nwith open('{output_file}', 'w') as f:\n    f.write(str(drawed_texts))\n"
    full_code = code + suffix
    savefig_idx = full_code.find("plt.savefig")
    ax_ticks_del = (
        "\nall_axes = plt.gcf().get_axes()\n"
        "for ax in all_axes:\n"
        "    ax.set_xticks([])\n"
        "    ax.set_yticks([])\n"
    )
    corrupted = full_code[:savefig_idx] + ax_ticks_del + full_code[savefig_idx:]
    return savefig_idx, corrupted


def plot2code_position_similarity(
    pos1: Tuple[float, float], pos2: Tuple[float, float], size_ratio: Tuple[float, float]
) -> float:
    """Exact port of TencentARC/Plot2Code@12bd95a7 text_match_score.py:20-31."""
    dx = pos1[0] - pos2[0] * size_ratio[0]
    dy = pos1[1] - pos2[1] * size_ratio[1]
    dist = math.hypot(dx, dy)
    return math.exp(-dist / 100.0)


def plot2code_match_texts(
    texts1: Sequence[str],
    texts2: Sequence[str],
    pos1: Sequence[Tuple[float, float]],
    pos2: Sequence[Tuple[float, float]],
    size_ratio: Tuple[float, float],
) -> float:
    """Exact port of Plot2Code text_match_score.py:51-81 (min_distance <= 0 exact match)."""
    t2 = list(texts2)
    p2 = list(pos2)
    matched = 0
    unmatched1 = len(texts1)
    unmatched2 = len(t2)
    for text1, q1 in zip(texts1, pos1):
        min_dist = math.inf
        best_idx = None
        for idx, (text2, q2) in enumerate(zip(t2, p2)):
            # Exact Levenshtein distance == 0 iff strings equal; for distance > 0, line 70 rejects anyway
            dist = 0 if text1 == text2 else max(len(text1), len(text2))
            psim = plot2code_position_similarity(q1, q2, size_ratio)
            if dist < min_dist and psim > 0.8:
                min_dist = dist
                best_idx = idx
        if min_dist <= 0 and best_idx is not None:
            matched += 1
            t2.pop(best_idx)
            p2.pop(best_idx)
            unmatched2 -= 1
            unmatched1 -= 1
    total_pairs = matched + unmatched1 + unmatched2
    return 1.0 if total_pairs == 0 else matched / total_pairs


def run_probe_2() -> None:
    print("\n========================================================================")
    print("PROBE 2: ChartMimic (@92ba5b97) & Plot2Code (@12bd95a7) Evaluator Forensics")
    print("Provenance: [exact port of pinned evaluator logic] + [controlled simulation]")
    print("========================================================================")

    # 2A. ChartMimic ChartTypeEvaluator state-carryover inflation sweep
    n_charts = 600
    # Conditional success F1 = 0.80 (4 correct of 5 calls -> P=0.8, R=0.8, F1=0.8)
    gold_sample = {"bar": 4, "line": 1}
    succ_gen = {"bar": 4, "scatter": 1}  # n_correct=4, P=0.8, R=0.8, F1=0.8
    cond_f1 = 0.80

    # Failure rates spanning ChartMimic Table 3 (GPT-4o 6.8% up to DeepSeek-VL-7B 58.7%)
    failure_rates = [0.068, 0.200, 0.400, 0.587]
    print("  [ChartMimic] ChartTypeEvaluator state-carryover bug (N=600, conditional F1=0.800):")
    for fail_rate in failure_rates:
        rng = random.Random(202601 + int(fail_rate * 1000))
        buggy = ChartTypeEvaluatorBuggy()
        fixed = ChartTypeEvaluatorFixed()
        buggy_f1s = []
        fixed_f1s = []
        for _ in range(n_charts):
            is_fail = rng.random() < fail_rate
            gen = {} if is_fail else succ_gen
            buggy_f1s.append(buggy.evaluate(gen, gold_sample)["f1"])
            fixed_f1s.append(fixed.evaluate(gen, gold_sample)["f1"])
        mean_buggy = sum(buggy_f1s) / n_charts
        mean_fixed = sum(fixed_f1s) / n_charts
        delta_f1 = mean_buggy - mean_fixed
        inflation_ratio = mean_buggy / mean_fixed
        # Analytical closed-form: E[buggy] = cond_f1 * (1 - (1 - f^N)/(N*(1-f)) * f) ~ cond_f1
        theo_inflation = fail_rate * cond_f1
        assert abs(delta_f1 - theo_inflation) < 0.035
        assert mean_buggy > mean_fixed + 0.04
        print(
            f"    fail_rate={fail_rate*100:5.1f}% | true_F1={mean_fixed:.4f} | "
            f"buggy_F1={mean_buggy:.4f} | +delta={delta_f1:+.4f} ({inflation_ratio:.2f}x)"
        )

    # 2B. ChartMimic text_evaluator.py:49,52-56,165-178 `-1` slice bug on fig.savefig()
    fig_script = "import matplotlib.pyplot as plt\nfig, ax = plt.subplots()\nax.plot([1,2],[3,4])\nfig.savefig('out.pdf')\n"
    idx_fig, out_fig = chartmimic_text_injector(fig_script, "out_log_texts.txt")
    assert idx_fig == -1
    # Because pinned suffix (L166-170) ends with '\n', code[:-1] compiles cleanly and inserts
    # tick-deletion AFTER both fig.savefig() AND f.write(...) -> silent tick contamination!
    compile(out_fig, "<pinned_text_evaluator>", "exec")
    pos_savefig = out_fig.find("fig.savefig")
    pos_fwrite = out_fig.find("f.write(str(drawed_texts))")
    pos_tickdel = out_fig.find("ax.set_xticks([])")
    assert pos_savefig < pos_fwrite < pos_tickdel
    # Note: a SyntaxError via `code[:-1]` occurs only if a caller omits a trailing newline on the
    # post-suffix string (unreachable in pinned text_evaluator.py because suffix ends with '\n').
    print(
        f"  [ChartMimic] text_evaluator.py find('plt.savefig') on fig.savefig(): idx={idx_fig} | "
        f"compiles cleanly, placing tick-deletion AFTER fig.savefig() & f.write() "
        f"(pos {pos_tickdel} > {pos_fwrite}; silent tick contamination)"
    )

    # 2C. ChartMimic color_evaluator.py:160-219 P(n,k) vs O(n^3) Hungarian optimal assignment
    # Note: upstream groups colors by chart-element type and deduplicates via filter_color (sim > 0.7)
    # at L194-205 before enumerating P(n, k) permutations over the surviving distinct-color palette.
    rng_c = random.Random(42)
    n_verify = 6
    sim_mat = [[rng_c.uniform(0.1, 1.0) for _ in range(n_verify)] for _ in range(n_verify)]
    best_perm = max(
        sum(sim_mat[i][perm[i]] for i in range(n_verify))
        for perm in permutations(range(n_verify))
    )
    neg_cost = [[-v for v in row] for row in sim_mat]
    hung_pairs = linear_sum_assignment(neg_cost)
    best_hung = sum(sim_mat[r][c] for r, c in hung_pairs)
    assert abs(best_perm - best_hung) < 1e-12
    perm_counts = {n: math.factorial(n) for n in (4, 6, 8, 9, 10, 12)}
    assert perm_counts[12] == 479_001_600 and perm_counts[12] // (12 ** 3) == 277_200
    print(
        f"  [ChartMimic] color_evaluator P(n,n) (post-filter_color) vs O(n^3): n=6 exact match={best_perm:.6f}=={best_hung:.6f} | "
        f"n=9: {perm_counts[9]:,} vs {9**3}; n=12: {perm_counts[12]:,} vs {12**3} ({perm_counts[12]//(12**3):,}x)"
    )

    # 2D. Plot2Code text_match_score.py:20-81 coordinate-space mixing & vacuity
    d_threshold = -100.0 * math.log(0.8)  # 22.314355
    min_axes_sim = plot2code_position_similarity((0.0, 0.0), (1.0, 1.0), (1.0, 1.0))
    assert abs(d_threshold - 22.314355131420976) < 1e-9
    assert abs(min_axes_sim - math.exp(-math.sqrt(2.0) / 100.0)) < 1e-12
    assert min_axes_sim > 0.9859

    # Opposite-corner swap of title (0.5,1.0) and xlabel (0.5,0.0) in axes-fraction space
    score_swapped_axes = plot2code_match_texts(
        ["annual revenue", "fiscal year"],
        ["fiscal year", "annual revenue"],
        [(0.5, 1.0), (0.5, 0.0)],
        [(0.5, 1.0), (0.5, 0.0)],
        (1.0, 1.0),
    )
    assert score_swapped_axes == 1.0

    # Data-space annotation [0, 1000]: tiny 2.5% shift (25 units) fails!
    sim_data_shift = plot2code_position_similarity((500.0, 500.0), (525.0, 500.0), (1.0, 1.0))
    score_data_shift = plot2code_match_texts(["peak"], ["peak"], [(500.0, 500.0)], [(525.0, 500.0)], (1.0, 1.0))
    assert sim_data_shift < 0.8 and score_data_shift == 0.0

    # Identical data-space coordinate (500,500) with figsize (6,4) vs (12,8) -> size_ratio=(0.5,0.5) FALSE FAIL!
    sim_figsize = plot2code_position_similarity((500.0, 500.0), (500.0, 500.0), (0.5, 0.5))
    score_figsize = plot2code_match_texts(["peak"], ["peak"], [(500.0, 500.0)], [(500.0, 500.0)], (0.5, 0.5))
    assert sim_figsize < 0.05 and score_figsize == 0.0

    print(
        f"  [Plot2Code] text_match_score.py threshold: exp(-d/100)>0.8 <=> d<{d_threshold:.3f} (mixed units)"
    )
    print(
        f"    Axes-fraction [0,1]^2 worst-case opposite corners: sim={min_axes_sim:.6f} (>0.8 vacuous!), swapped title/xlabel score={score_swapped_axes:.4f}"
    )
    print(
        f"    Data-space [0,1000] 2.5% shift (25u): sim={sim_data_shift:.4f} -> score={score_data_shift:.4f} | "
        f"identical data pos w/ 2x figsize: sim={sim_figsize:.4f} -> score={score_figsize:.4f}"
    )


# ============================================================================
# PROBE 3: pixelmatch v7.1.1 (YIQ) & post-v8.0.0 (OKLab HyAB) vs DOM Oracle
# ============================================================================

# Precomputed LUTs matching mapbox/pixelmatch@ab76f526 (post-v8.0.0) index.js:299-362
_PM8_LIN = [
    (i / 255.0) / 12.92 if (i / 255.0) <= 0.04045 else (((i / 255.0) + 0.055) / 1.055) ** 2.4
    for i in range(256)
]
_PM8_LIN.append(_PM8_LIN[255])

_PM8_LR = [0.4122214708 * v for v in _PM8_LIN[:256]]
_PM8_MR = [0.2119034982 * v for v in _PM8_LIN[:256]]
_PM8_SR = [0.0883024619 * v for v in _PM8_LIN[:256]]
_PM8_LG = [0.5363325363 * v for v in _PM8_LIN[:256]]
_PM8_MG = [0.6806995451 * v for v in _PM8_LIN[:256]]
_PM8_SG = [0.2817188376 * v for v in _PM8_LIN[:256]]
_PM8_LB = [0.0514459929 * v for v in _PM8_LIN[:256]]
_PM8_MB = [0.1073969566 * v for v in _PM8_LIN[:256]]
_PM8_SB = [0.6299787005 * v for v in _PM8_LIN[:256]]

_PM8_CBRT_N = 4096
_PM8_CBRT = [math.cbrt(i / _PM8_CBRT_N) for i in range(_PM8_CBRT_N + 2)]
_PM8_CBRT_EXACT = 8
_PM8_TOE_K1 = 0.206
_PM8_TOE_K2 = 0.03
_PM8_TOE_K3 = (1.0 + _PM8_TOE_K1) / (1.0 + _PM8_TOE_K2)


def _pm8_cbrt_lut(x: float) -> float:
    t = x * _PM8_CBRT_N
    i = int(t)
    if i < _PM8_CBRT_EXACT:
        return math.cbrt(x)
    return _PM8_CBRT[i] + (_PM8_CBRT[i + 1] - _PM8_CBRT[i]) * (t - i)


def _pm8_lightness(l: float, m: float, s: float) -> float:
    L = 0.2104542553 * l + 0.7936177850 * m - 0.0040720468 * s
    x = _PM8_TOE_K3 * L - _PM8_TOE_K1
    return 0.5 * (x + math.sqrt(x * x + 4.0 * _PM8_TOE_K2 * _PM8_TOE_K3 * L))


def _pm8_opaque_lr(r: int, g: int, b: int) -> float:
    """Compute OKLab toe-corrected lightness Lr for an opaque RGB pixel."""
    l = _pm8_cbrt_lut(_PM8_LR[r] + _PM8_LG[g] + _PM8_LB[b])
    m = _pm8_cbrt_lut(_PM8_MR[r] + _PM8_MG[g] + _PM8_MB[b])
    s = _pm8_cbrt_lut(_PM8_SR[r] + _PM8_SG[g] + _PM8_SB[b])
    return _pm8_lightness(l, m, s)


def _pm7_color_delta(img1: bytearray, img2: bytearray, k: int) -> float:
    """Exact port of mapbox/pixelmatch@973afc76 (v7.1.1) index.js:210-242."""
    r1, g1, b1, a1 = img1[k], img1[k + 1], img1[k + 2], img1[k + 3]
    r2, g2, b2, a2 = img2[k], img2[k + 1], img2[k + 2], img2[k + 3]
    dr = r1 - r2
    dg = g1 - g2
    db = b1 - b2
    da = a1 - a2
    if a1 < 255 or a2 < 255:
        rb = 48 + 159 * (k % 2)
        gb = 48 + 159 * (int(k / 1.618033988749895) % 2)
        bb = 48 + 159 * (int(k / 2.618033988749895) % 2)
        dr = (r1 * a1 - r2 * a2 - rb * da) / 255.0
        dg = (g1 * a1 - g2 * a2 - gb * da) / 255.0
        db = (b1 * a1 - b2 * a2 - bb * da) / 255.0
    y = dr * 0.29889531 + dg * 0.58662247 + db * 0.11448223
    i = dr * 0.59597799 - dg * 0.27417610 - db * 0.32180189
    q = dr * 0.21147017 - dg * 0.52261711 + db * 0.31114694
    delta = 0.5053 * y * y + 0.299 * i * i + 0.1957 * q * q
    return -delta if y > 0.0 else delta


def _pm8_color_delta_opaque(
    r1: int, g1: int, b1: int, r2: int, g2: int, b2: int, max_delta: float
) -> int:
    """Exact port of mapbox/pixelmatch@ab76f526 (post-v8.0.0) opaque fast path (index.js:408-454, 510-534)."""
    l1 = _pm8_cbrt_lut(_PM8_LR[r1] + _PM8_LG[g1] + _PM8_LB[b1])
    m1 = _pm8_cbrt_lut(_PM8_MR[r1] + _PM8_MG[g1] + _PM8_MB[b1])
    s1 = _pm8_cbrt_lut(_PM8_SR[r1] + _PM8_SG[g1] + _PM8_SB[b1])
    lr1 = _pm8_lightness(l1, m1, s1)

    l2 = _pm8_cbrt_lut(_PM8_LR[r2] + _PM8_LG[g2] + _PM8_LB[b2])
    m2 = _pm8_cbrt_lut(_PM8_MR[r2] + _PM8_MG[g2] + _PM8_MB[b2])
    s2 = _pm8_cbrt_lut(_PM8_SR[r2] + _PM8_SG[g2] + _PM8_SB[b2])
    lr2 = _pm8_lightness(l2, m2, s2)

    d_lr = lr1 - lr2
    rest = max_delta - abs(d_lr)
    if rest >= 0.0:
        dl, dm, ds = l1 - l2, m1 - m2, s1 - s2
        da = 1.9779984951 * dl - 2.4285922050 * dm + 0.4505937099 * ds
        db = 0.0259040371 * dl + 0.7827717662 * dm - 0.8086757660 * ds
        if da * da + db * db <= rest * rest:
            return 0
    return -1 if d_lr > 0.0 else 1


def _pm_brightness_delta(
    img: bytearray, m: int, r1: int, g1: int, b1: int, a1: int
) -> float:
    """Rec.601 luma delta from pixelmatch@ab76f526 (post-v8.0.0 index.js:558-580).

    Uses v8's white-background + da/2 semi-transparent branch (v7.1.1 index.js:268-275
    blended semi-transparent pixels over a checkerboard without da/2); both are
    bit-identical on Probe 3's opaque (a=255) images.
    """
    r2, g2, b2, a2 = img[m], img[m + 1], img[m + 2], img[m + 3]
    dr, dg, db, da = r1 - r2, g1 - g2, b1 - b2, a1 - a2
    if dr == 0 and dg == 0 and db == 0 and da == 0:
        return 0.0
    if a1 < 255 or a2 < 255:
        dr_f = (r1 * a1 - r2 * a2 - 255 * da) / 255.0
        dg_f = (g1 * a1 - g2 * a2 - 255 * da) / 255.0
        db_f = (b1 * a1 - b2 * a2 - 255 * da) / 255.0
        d = dr_f * 0.29889531 + dg_f * 0.58662247 + db_f * 0.11448223
        return da / 2.0 if (d == 0.0 and da != 0) else d
    return dr * 0.29889531 + dg * 0.58662247 + db * 0.11448223


def _pm_has_many_siblings(a32: List[int], x1: int, y1: int, width: int, height: int) -> bool:
    """Exact port of pixelmatch hasManySiblings (v7.1.1:182-199 & post-v8.0.0:280-297)."""
    x0 = max(x1 - 1, 0)
    y0 = max(y1 - 1, 0)
    x2 = min(x1 + 1, width - 1)
    y2 = min(y1 + 1, height - 1)
    val = a32[y1 * width + x1]
    zeroes = 1 if (x1 == x0 or x1 == x2 or y1 == y0 or y1 == y2) else 0
    for x in range(x0, x2 + 1):
        for y in range(y0, y2 + 1):
            if x == x1 and y == y1:
                continue
            if val == a32[y * width + x]:
                zeroes += 1
                if zeroes > 2:
                    return True
    return False


def _pm_antialiased(
    img: bytearray, x1: int, y1: int, width: int, height: int, a32: List[int], b32: List[int]
) -> bool:
    """Exact port of pixelmatch 8-neighbor Vysniauskas AA detector."""
    x0 = max(x1 - 1, 0)
    y0 = max(y1 - 1, 0)
    x2 = min(x1 + 1, width - 1)
    y2 = min(y1 + 1, height - 1)
    pos4 = (y1 * width + x1) * 4
    cr, cg, cb, ca = img[pos4], img[pos4 + 1], img[pos4 + 2], img[pos4 + 3]
    zeroes = 1 if (x1 == x0 or x1 == x2 or y1 == y0 or y1 == y2) else 0
    min_d = 0.0
    max_d = 0.0
    min_x = min_y = max_x = max_y = 0

    for x in range(x0, x2 + 1):
        for y in range(y0, y2 + 1):
            if x == x1 and y == y1:
                continue
            delta = _pm_brightness_delta(img, (y * width + x) * 4, cr, cg, cb, ca)
            if delta == 0.0:
                zeroes += 1
                if zeroes > 2:
                    return False
            elif delta < min_d:
                min_d = delta
                min_x, min_y = x, y
            elif delta > max_d:
                max_d = delta
                max_x, max_y = x, y

    if min_d == 0.0 or max_d == 0.0:
        return False

    return (
        (_pm_has_many_siblings(a32, min_x, min_y, width, height)
         and _pm_has_many_siblings(b32, min_x, min_y, width, height))
        or (_pm_has_many_siblings(a32, max_x, max_y, width, height)
            and _pm_has_many_siblings(b32, max_x, max_y, width, height))
    )


def _pack_rgba32(img: bytearray) -> List[int]:
    return [
        img[p] | (img[p + 1] << 8) | (img[p + 2] << 16) | (img[p + 3] << 24)
        for p in range(0, len(img), 4)
    ]


def _pm8_max_window_sum(mask: bytearray, width: int, height: int, window_size: int) -> int:
    """Exact port of pixelmatch@ab76f526 index.js:123-180 sliding N x N max-diff pass."""
    n = min(max(int(window_size), 1), width, height)
    col_sum = [0] * width
    max_window = 0
    for y in range(height):
        row_start = y * width
        leaving = y - n
        if leaving >= 0:
            leave_start = leaving * width
            for x in range(width):
                col_sum[x] += mask[row_start + x] - mask[leave_start + x]
        else:
            for x in range(width):
                col_sum[x] += mask[row_start + x]
            if y < n - 1:
                continue
        wsum = sum(col_sum[: n - 1])
        for x in range(n - 1, width):
            wsum += col_sum[x]
            if wsum > max_window:
                max_window = wsum
            wsum -= col_sum[x - n + 1]
    return max_window


def pixelmatch_run(
    img1: bytearray,
    img2: bytearray,
    width: int,
    height: int,
    engine: str = "v7_yiq",
    threshold: float = 0.1,
    include_aa: bool = False,
    window_sizes: Sequence[int] = (),
) -> Dict[str, object]:
    """Run pixelmatch v7.1.1 (YIQ) or post-v8.0.0 (OKLab HyAB opaque fast path + windowSize)."""
    a32 = _pack_rgba32(img1)
    b32 = _pack_rgba32(img2)
    n_pix = width * height
    max_yiq = 35215.0 * threshold * threshold
    diff_count = 0
    aa_excluded = 0
    mask = bytearray(n_pix) if window_sizes else None

    for i in range(n_pix):
        if a32[i] == b32[i]:
            continue
        pos = i * 4
        if engine == "v7_yiq":
            exceeds = abs(_pm7_color_delta(img1, img2, pos)) > max_yiq
        else:
            exceeds = _pm8_color_delta_opaque(
                img1[pos], img1[pos + 1], img1[pos + 2],
                img2[pos], img2[pos + 1], img2[pos + 2],
                threshold,
            ) != 0
        if not exceeds:
            continue
        x = i % width
        y = i // width
        is_aa = (not include_aa) and (
            _pm_antialiased(img1, x, y, width, height, a32, b32)
            or _pm_antialiased(img2, x, y, width, height, b32, a32)
        )
        if is_aa:
            aa_excluded += 1
        else:
            diff_count += 1
            if mask is not None:
                mask[i] = 1

    windows: Dict[int, int] = {}
    if mask is not None:
        for ws in window_sizes:
            windows[ws] = _pm8_max_window_sum(mask, width, height, ws) if diff_count > 0 else 0

    return {"diff": diff_count, "aa_excluded": aa_excluded, "windows": windows}


# Minimal crisp 5x7 pixel font for synthetic financial UI card rendering
_FONT_5X7: Dict[str, Tuple[str, ...]] = {
    "$": ("..#..", ".####", "#.#..", ".###.", "..#.#", "####.", "..#.."),
    "1": ("..#..", ".##..", "..#..", "..#..", "..#..", "..#..", ".###."),
    "0": (".###.", "#...#", "#..##", "#.#.#", "##..#", "#...#", ".###."),
    "9": (".###.", "#...#", "#...#", ".####", "....#", "...#.", ".##.."),
    "2": (".###.", "#...#", "....#", "..##.", ".#...", "#....", "#####"),
    "+": (".....", "..#..", "..#..", "#####", "..#..", "..#..", "....."),
    "-": (".....", ".....", ".....", "#####", ".....", ".....", "....."),
    ".": (".....", ".....", ".....", ".....", ".....", ".##..", ".##.."),
    "%": ("##..#", "##.#.", "..#..", ".#...", "#..##", "...##", "....."),
    "P": ("####.", "#...#", "#...#", "####.", "#....", "#....", "#...."),
    "a": (".....", ".....", ".###.", "....#", ".####", "#...#", ".####"),
    "s": (".....", ".....", ".####", "#....", ".###.", "....#", "####."),
    "F": ("#####", "#....", "#....", "####.", "#....", "#....", "#...."),
    "i": ("..#..", ".....", ".##..", "..#..", "..#..", "..#..", ".###."),
    "l": (".##..", "..#..", "..#..", "..#..", "..#..", "..#..", ".###."),
    " ": (".....", ".....", ".....", ".....", ".....", ".....", "....."),
}


def _render_ui_card(
    width: int,
    height: int,
    price: str,
    delta: str,
    status: str,
    shift_x: int = 0,
    aa_edge_gray: int = 135,
    card_bg: Tuple[int, int, int] = (248, 250, 252),
) -> Tuple[bytearray, List[dict]]:
    """Render deterministic synthetic opaque (a=255) UI card RGBA buffer + structured DOM tree."""
    buf = bytearray([255, 255, 255, 255] * (width * height))

    def set_px(x: int, y: int, rgb: Tuple[int, int, int]) -> None:
        if 0 <= x < width and 0 <= y < height:
            p = (y * width + x) * 4
            buf[p], buf[p + 1], buf[p + 2], buf[p + 3] = rgb[0], rgb[1], rgb[2], 255

    def fill_rect(x0: int, y0: int, w: int, h: int, rgb: Tuple[int, int, int]) -> None:
        for y in range(max(0, y0), min(height, y0 + h)):
            for x in range(max(0, x0), min(width, x0 + w)):
                set_px(x, y, rgb)

    # Card container with 2px solid border + 1px outer anti-aliased edge
    cx, cy, cw, ch = 12 + shift_x, 12, 212, 92
    fill_rect(cx - 1, cy - 1, cw + 2, ch + 2, (aa_edge_gray, aa_edge_gray, aa_edge_gray))
    fill_rect(cx, cy, cw, ch, (30, 41, 59))
    fill_rect(cx + 2, cy + 2, cw - 4, ch - 4, card_bg)

    def draw_text(text: str, x0: int, y0: int, fg: Tuple[int, int, int], scale: int = 2) -> None:
        cur_x = x0
        for ch_sym in text:
            glyph = _FONT_5X7[ch_sym]
            for gy, row in enumerate(glyph):
                for gx, bit in enumerate(row):
                    if bit == "#":
                        fill_rect(cur_x + gx * scale, y0 + gy * scale, scale, scale, fg)
            cur_x += (5 + 1) * scale

    # Draw text with 1px horizontal AA halo below the dark banner stripe
    fill_rect(cx + 12, cy + 12, 188, 12, (20, 30, 50))
    fill_rect(cx + 12, cy + 24, 188, 1, (aa_edge_gray, aa_edge_gray, aa_edge_gray))
    draw_text(price, cx + 16, cy + 34, (15, 23, 42), scale=2)
    draw_text(delta, cx + 100, cy + 34, (22, 101, 52), scale=2)
    draw_text(status, cx + 16, cy + 66, (30, 64, 175), scale=2)

    dom = [
        {"id": "card",   "text": "",     "bbox": (cx, cy, cw, ch)},
        {"id": "price",  "text": price,  "bbox": (cx + 16, cy + 34, len(price) * 12, 14)},
        {"id": "delta",  "text": delta,  "bbox": (cx + 100, cy + 34, len(delta) * 12, 14)},
        {"id": "status", "text": status, "bbox": (cx + 16, cy + 66, len(status) * 12, 14)},
    ]
    return buf, dom


def structured_dom_diff(ref_dom: List[dict], cand_dom: List[dict], pos_tol_px: int = 2) -> Dict[str, int]:
    """Compare text semantics and relative intra-card geometry invariant to uniform 1-2px shifts."""
    ref_map = {n["id"]: n for n in ref_dom}
    cand_map = {n["id"]: n for n in cand_dom}
    text_mismatches = 0
    geom_mismatches = 0
    ref_root = ref_map["card"]["bbox"]
    cand_root = cand_map["card"]["bbox"]
    for nid in sorted(ref_map.keys()):
        rn, cn = ref_map[nid], cand_map[nid]
        if rn["text"] != cn["text"]:
            text_mismatches += 1
        rx, ry, rw, rh = rn["bbox"]
        cx, cy, cw, ch = cn["bbox"]
        rel_dx = abs((cx - cand_root[0]) - (rx - ref_root[0]))
        rel_dy = abs((cy - cand_root[1]) - (ry - ref_root[1]))
        if rel_dx > pos_tol_px or rel_dy > pos_tol_px or abs(cw - rw) > pos_tol_px or abs(ch - rh) > pos_tol_px:
            geom_mismatches += 1
    return {"text_mismatches": text_mismatches, "geom_mismatches": geom_mismatches}


def run_probe_3() -> None:
    print("\n========================================================================")
    print("PROBE 3: pixelmatch v7.1.1 (@973afc76) & post-v8.0.0 (@ab76f526) vs. DOM Oracle")
    print("Provenance: [exact port of pinned opaque-pixel logic] + [controlled simulation]")
    print("========================================================================")

    # Exact YIQ maximum verification: 35,214.75 is achieved by Red (255,0,0) vs Cyan (0,255,255),
    # whereas Black (0,0,0) vs White (255,255,255) is only 32,857.13 (0.5053 * 255^2, 93.3% of max).
    rc1 = bytearray([255, 0, 0, 255])
    rc2 = bytearray([0, 255, 255, 255])
    yiq_max = abs(_pm7_color_delta(rc1, rc2, 0))
    bw1 = bytearray([0, 0, 0, 255])
    bw2 = bytearray([255, 255, 255, 255])
    yiq_bw = abs(_pm7_color_delta(bw1, bw2, 0))
    assert abs(yiq_max - 35214.7490) < 0.01
    assert abs(yiq_bw - 32857.1332) < 0.01
    assert _pm8_color_delta_opaque(0, 0, 0, 255, 255, 255, 0.1) == 1

    # Dark-region perceptual divergence between v7.1.1 YIQ and post-v8.0.0 OKLab HyAB
    # (12,12,12) vs (38,38,38): YIQ delta = 0.5053 * 26^2 = 341.58 <= 352.15 (PASSES v7 at t=0.1)
    # while OKLab toe-corrected |dLr| = 0.103460 (~0.1035) > 0.10 (CAUGHT by post-v8.0.0 at t=0.1).
    d1 = bytearray([12, 12, 12, 255])
    d2 = bytearray([38, 38, 38, 255])
    yiq_dark = abs(_pm7_color_delta(d1, d2, 0))
    abs_dlr_dark = abs(_pm8_opaque_lr(12, 12, 12) - _pm8_opaque_lr(38, 38, 38))
    oklab_dark = _pm8_color_delta_opaque(12, 12, 12, 38, 38, 38, 0.1)
    assert yiq_dark <= 352.15 and abs(abs_dlr_dark - 0.103460) < 1e-5 and oklab_dark != 0

    w, h = 240, 120
    crop_pixels = w * h          # 28,800 px standalone card crop
    full_vp_pixels = 1280 * 720  # 921,600 px desktop viewport assuming static surround
    ws_sweep = (4, 8, 12, 16, 24, 32)
    base_img, base_dom = _render_ui_card(w, h, "$100", "+1.2%", "Pass", shift_x=0, aa_edge_gray=135)

    scenarios = [
        ("1px_horizontal_shift", _render_ui_card(w, h, "$100", "+1.2%", "Pass", shift_x=1, aa_edge_gray=135)),
        ("benign_aa_ramp_tweak", _render_ui_card(w, h, "$100", "+1.2%", "Pass", shift_x=0, aa_edge_gray=175)),
        ("semantic_sign_only",   _render_ui_card(w, h, "$100", "-1.2%", "Pass", shift_x=0, aa_edge_gray=135)),
        ("semantic_digit_sign",  _render_ui_card(w, h, "$900", "-1.2%", "Pass", shift_x=0, aa_edge_gray=135)),
        ("semantic_status_flip", _render_ui_card(w, h, "$100", "+1.2%", "Fail", shift_x=0, aa_edge_gray=135)),
    ]

    results = {}
    for name, (cand_img, cand_dom) in scenarios:
        r7 = pixelmatch_run(base_img, cand_img, w, h, engine="v7_yiq", threshold=0.1)
        r8 = pixelmatch_run(base_img, cand_img, w, h, engine="v8_oklab", threshold=0.1, window_sizes=ws_sweep)
        dom_res = structured_dom_diff(base_dom, cand_dom)
        crop_ratio = r7["diff"] / crop_pixels
        vp_ratio = r7["diff"] / full_vp_pixels
        results[name] = (r7, r8, dom_res, crop_ratio, vp_ratio)
        wmap = r8["windows"]
        print(
            f"  {name:20s} | diff={r7['diff']:3d} (AA={r7['aa_excluded']:3d}, crop={crop_ratio*100:.4f}%, "
            f"720p_static={vp_ratio*100:.4f}%) | v8_win[8/12/16]={wmap[8]:3d}/{wmap[12]:3d}/{wmap[16]:3d} | "
            f"DOM text_err={dom_res['text_mismatches']} geom_err={dom_res['geom_mismatches']}"
        )

    # Window-size phase transition sweep (4, 8, 12, 16, 24, 32)
    w_shift = results["1px_horizontal_shift"][1]["windows"]
    w_sign = results["semantic_sign_only"][1]["windows"]
    w_dign = results["semantic_digit_sign"][1]["windows"]

    # Non-vacuous assertions:
    # 1. 1px shift causes massive pixel diff (600 px) yet 0 DOM semantic/relative-geometry errors
    assert results["1px_horizontal_shift"][0]["diff"] == 600
    assert results["1px_horizontal_shift"][1]["diff"] == 600
    assert results["1px_horizontal_shift"][2] == {"text_mismatches": 0, "geom_mismatches": 0}

    # 2. Benign AA ramp tweak is >=98% filtered by 8-neighbor antialiased() in BOTH v7 and v8
    aa7_frac = results["benign_aa_ramp_tweak"][0]["aa_excluded"] / (
        results["benign_aa_ramp_tweak"][0]["diff"] + results["benign_aa_ramp_tweak"][0]["aa_excluded"]
    )
    aa8_frac = results["benign_aa_ramp_tweak"][1]["aa_excluded"] / (
        results["benign_aa_ramp_tweak"][1]["diff"] + results["benign_aa_ramp_tweak"][1]["aa_excluded"]
    )
    assert aa7_frac >= 0.98 and aa8_frac >= 0.98

    # 3. Phase transition on compact glyph+sign corruption (semantic_digit_sign, 84 px):
    #    - Global diff: 84 px (0.2917% of 240x120 crop, 0.0091% of static 720p) << 600 px 1px shift (>7x smaller).
    #    - Fine windows (ws in {4, 8, 12}): semantic_digit_sign > 1px_shift (SEPARABLE on this canvas!).
    #    - Coarse windows (ws in {16, 24, 32}): semantic_digit_sign < 1px_shift (NON-SEPARABLE).
    assert results["semantic_digit_sign"][0]["diff"] == 84
    assert results["semantic_digit_sign"][4] < 0.0001
    for ws in (4, 8, 12):
        assert w_dign[ws] > w_shift[ws], f"Expected separable at ws={ws}: {w_dign[ws]} vs {w_shift[ws]}"
    for ws in (16, 24, 32):
        assert w_dign[ws] < w_shift[ws], f"Expected non-separable at ws={ws}: {w_dign[ws]} vs {w_shift[ws]}"
    assert results["semantic_digit_sign"][2]["text_mismatches"] == 2

    # 4. Thin-stroke sign flip (+1.2% -> -1.2% alone, 16 px):
    #    - Global diff: 16 px (0.0556% crop, 0.0017% static 720p; 37.5x smaller than 1px shift).
    #    - Local windows: <= 1px_shift at EVERY ws in {4, 8, 12, 16, 24, 32} (tied 8==8 at ws=4;
    #      strictly below 1px_shift for all ws >= 8), while DOM oracle catches text_err=1!
    assert results["semantic_sign_only"][0]["diff"] == 16
    assert w_sign[4] <= w_shift[4]
    for ws in (8, 12, 16, 24, 32):
        assert w_sign[ws] < w_shift[ws], f"Expected sign-only < shift at ws={ws}: {w_sign[ws]} vs {w_shift[ws]}"
    assert results["semantic_sign_only"][2]["text_mismatches"] == 1
    assert results["semantic_status_flip"][2]["text_mismatches"] == 1

    print("  post-v8.0.0 windowSize sweep [4, 8, 12, 16, 24, 32]:")
    print("    1px_horizontal_shift: " + ", ".join(f"ws{ws}={w_shift[ws]}" for ws in ws_sweep))
    print("    semantic_digit_sign : " + ", ".join(f"ws{ws}={w_dign[ws]}" for ws in ws_sweep) + " (separable <=12; dominated >=16)")
    print("    semantic_sign_only  : " + ", ".join(f"ws{ws}={w_sign[ws]}" for ws in ws_sweep) + " (tied ws4; dominated >=8)")
    print(
        f"  v7 YIQ max constant check: Red(255,0,0) vs Cyan(0,255,255)={yiq_max:.2f} (~35215), "
        f"Black vs White={yiq_bw:.2f} ({100*yiq_bw/yiq_max:.1f}% of max)"
    )
    print(
        f"  Dark-gray divergence (12,12,12) vs (38,38,38) at t=0.1: "
        f"v7_YIQ={yiq_dark:.2f}<=352.15 (PASS), post-v8.0.0 |dLr|={abs_dlr_dark:.6f} (>0.10, DIFF={oklab_dark}) | "
        f"AA ramp exclusion={aa7_frac*100:.1f}%"
    )


# ============================================================================
# PROBE 4: axe-core / GOV.UK / WebAIM Coverage & ARIA Misuse Decomposition
# ============================================================================

# Exact verified 19-category detection matrix transcribed from
# alphagov/accessibility-tool-audit@e9e46115 (tests.json)
# Tuple: (category, total, axe_ew, axe_manual, union_13_ew, union_13_ewm)
GOVUK_MATRIX: Tuple[Tuple[str, int, int, int, int, int], ...] = (
    ("Content",              5,  0, 0,  2,  3),
    ("Page Layout",          1,  0, 0,  0,  0),
    ("Colour and Contrast",  6,  4, 0,  4,  6),
    ("Typography",           8,  2, 0,  6,  6),
    ("Language of content",  9,  4, 0,  6,  8),
    ("Page Title",           3,  2, 0,  2,  3),
    ("Headings",             4,  2, 0,  3,  3),
    ("Lists",                4,  3, 0,  3,  3),
    ("Tables",              11,  2, 0, 10, 10),
    ("Images",              10,  1, 0,  8, 10),
    ("Multimedia",           3,  0, 2,  2,  2),
    ("Links",               20,  4, 0, 18, 19),
    ("Buttons",              4,  3, 0,  4,  4),
    ("Forms",               19, 10, 0, 16, 19),
    ("Navigation",           1,  0, 0,  0,  0),
    ("Keyboard Access",     16,  1, 0,  7, 13),
    ("Frames",               2,  1, 0,  1,  2),
    ("CSS",                  5,  0, 0,  1,  3),
    ("HTML",                11,  2, 0,  7,  8),
)


def run_probe_4() -> None:
    print("\n========================================================================")
    print("PROBE 4: axe-core / GOV.UK / WebAIM Coverage & Parameterized Reconciliation")
    print("Provenance: [arithmetic verification on audited snapshots] + [derived analytical model]")
    print("========================================================================")

    # 4A. Accounting verification on audited W3C WCAG 2.2 & dequelabs/axe-core@e80f6b79 (v4.14.1) snapshots
    wcag22_active = {"A": 31, "AA": 24, "AAA": 31}
    wcag22_active_total = sum(wcag22_active.values())
    wcag22_active_aa = wcag22_active["A"] + wcag22_active["AA"]
    assert wcag22_active_total == 86 and wcag22_active_aa == 55

    axe_rule_catalog = {
        "wcag20_aa": 60, "wcag21_aa": 3, "wcag22_aa_optin": 1,
        "best_practice": 27, "wcag_aaa": 3, "experimental": 6, "deprecated": 5,
    }
    axe_wcag20_breakdown = {"failure_only": 17, "failure_and_review": 34, "review_only": 9}
    assert sum(axe_rule_catalog.values()) == 105
    assert sum(axe_wcag20_breakdown.values()) == axe_rule_catalog["wcag20_aa"]
    axe_sc_default_aa = 20
    axe_sc_unaddressed_aa = wcag22_active_aa - axe_sc_default_aa
    axe_sc_with_22 = 21       # adds opt-in disabled target-size (SC 2.5.8)
    axe_sc_all_105_aa = 23    # adds experimental (SC 1.3.4) & deprecated (SC 1.2.1)
    assert axe_sc_unaddressed_aa == 35
    assert abs(axe_sc_default_aa / wcag22_active_aa - 0.3636363636) < 1e-6

    # 4B. Accounting verification on audited alphagov/accessibility-tool-audit@e9e46115 snapshot
    tot_b = sum(r[1] for r in GOVUK_MATRIX)
    axe_ew = sum(r[2] for r in GOVUK_MATRIX)
    axe_man = sum(r[3] for r in GOVUK_MATRIX)
    u_ew = sum(r[4] for r in GOVUK_MATRIX)
    u_ewm = sum(r[5] for r in GOVUK_MATRIX)
    assert len(GOVUK_MATRIX) == 19 and tot_b == 142
    assert axe_ew == 41 and axe_man == 2 and u_ew == 100 and u_ewm == 122
    kb_row = [r for r in GOVUK_MATRIX if r[0] == "Keyboard Access"][0]
    img_row = [r for r in GOVUK_MATRIX if r[0] == "Images"][0]
    assert kb_row[2] / kb_row[1] == 1 / 16 and img_row[2] / img_row[1] == 1 / 10

    # 4C. Parameterized Volume-vs-Criteria Reconciliation (keeping Deque axe-core & WebAIM WAVE separated!)
    # Deque (axe-core audits): V_auto = 57.38%, V_non_auto = 42.62%, V_igt = 80.39%.
    # Let V_touched be total issue-volume share inside the 20 partially-automated A+AA SCs, and
    # r_auto in [V_auto, 1.0] be mean automated recall within those 20 SCs, so:
    #   V_auto = r_auto * V_touched = 0.5738
    #   V_non_auto (0.4262) = (1 - r_auto) * V_touched  [within-20 partial-recall misses]
    #                       + (1 - V_touched)           [35 unaddressed SCs]
    # Notice r_auto >= 0.5738 is required (since V_touched <= 1.0), and V_touched >= 0.5738 implies
    # >= 1.58x volume concentration on the 20 touched SCs relative to a uniform 20/55 = 36.36% split.
    deque_auto_vol = 0.5738
    deque_non_auto_vol = 1.0 - deque_auto_vol
    deque_igt_vol = 0.8039
    sc_share = axe_sc_default_aa / wcag22_active_aa
    min_concentration = deque_auto_vol / sc_share
    assert abs(min_concentration - 1.57795) < 1e-4

    recall_sweep = (0.65, 0.75, 0.85, 1.00)
    reconcil_rows = []
    for r_auto in recall_sweep:
        v_touched = deque_auto_vol / r_auto
        within_20_missed = (1.0 - r_auto) * v_touched
        uncovered_35_vol = 1.0 - v_touched
        conc = v_touched / sc_share
        assert 0.0 < v_touched <= 1.0 and within_20_missed >= 0.0 and uncovered_35_vol >= 0.0
        assert abs((deque_auto_vol + within_20_missed + uncovered_35_vol) - 1.0) < 1e-12
        assert abs((within_20_missed + uncovered_35_vol) - deque_non_auto_vol) < 1e-12
        reconcil_rows.append((r_auto, v_touched, within_20_missed, uncovered_35_vol, conc))

    # 4D. Verify A11yn (arXiv:2510.13914v2 Table 2) WVS weighting, cross-oracle gain, & residual gap
    a11yn_models = {
        "GPT-5.1":           (0, 163, 1118,  61,  3924, 0.13, 0.35),
        "Claude Sonnet 4.6": (7, 3044, 4885, 144, 21326, 0.45, 0.57),
        "Gemini 3 Pro":      (1, 1089,  908,  57,  5131, 0.24, 0.51),
        "Qwen2.5-7B Base":   (7,  951,  794,  47,  4479, 0.40, 0.62),
        "A11yn (GRPO-Axe)":  (0,   74,  138,  25,   662, 0.05, 0.26),
    }
    for mname, (mi, mo, se, cr, wvs, ir_axe, ir_ach) in a11yn_models.items():
        calc_wvs = 1 * mi + 2 * mo + 3 * se + 4 * cr
        assert calc_wvs == wvs, f"WVS mismatch for {mname}: {calc_wvs} != {wvs}"
    base_ir_ach = a11yn_models["Qwen2.5-7B Base"][6]
    a11yn_ir_ach = a11yn_models["A11yn (GRPO-Axe)"][6]
    ach_reduction_pct = (base_ir_ach - a11yn_ir_ach) / base_ir_ach * 100.0
    assert abs(ach_reduction_pct - 58.064516) < 1e-4
    # Confirm A11yn beats all 3 frontier models on IR_AChecker while retaining a 5.20x residual gap
    for frontier in ("GPT-5.1", "Claude Sonnet 4.6", "Gemini 3 Pro"):
        assert a11yn_ir_ach < a11yn_models[frontier][6]
    base_ratio = 0.62 / 0.40
    a11yn_ratio = 0.26 / 0.05
    assert abs(a11yn_ratio - 5.20) < 1e-9 and a11yn_ratio / base_ratio > 3.3

    # 4E. Simpson's-Paradox ARIA Complexity vs. Misuse Existence Witness (WebAIM 2026)
    # Exact published conservation check: 82.7% ARIA (59.1 errs) + 17.3% no-ARIA (42.0 errs) = 56.14 ~ 56.1
    p_aria_2026 = 0.827
    e_aria_2026, e_noaria_2026 = 59.1, 42.0
    weighted_2026 = p_aria_2026 * e_aria_2026 + (1.0 - p_aria_2026) * e_noaria_2026
    assert abs(weighted_2026 - 56.1) < 0.05

    # Two-stratum complexity model (Simple vs Complex DOM pages, calibrated to avg 1,437 elements):
    w_c, w_s = 0.72, 0.28
    p_a_given_c = 0.94
    p_a_given_s = (p_aria_2026 - w_c * p_a_given_c) / w_s
    avg_elems = w_c * 1700 + w_s * 760
    assert abs(avg_elems - 1436.8) < 1.0 and 0.0 < p_a_given_s < 1.0

    def marginal_aria_gap(err_s_no: float, err_c_no: float, causal_aria_delta_s: float, causal_aria_delta_c: float) -> Tuple[float, float, float]:
        p_c_given_a = (w_c * p_a_given_c) / p_aria_2026
        p_s_given_a = (w_s * p_a_given_s) / p_aria_2026
        p_c_given_no = (w_c * (1.0 - p_a_given_c)) / (1.0 - p_aria_2026)
        p_s_given_no = (w_s * (1.0 - p_a_given_s)) / (1.0 - p_aria_2026)
        e_a = p_c_given_a * (err_c_no + causal_aria_delta_c) + p_s_given_a * (err_s_no + causal_aria_delta_s)
        e_no = p_c_given_no * err_c_no + p_s_given_no * err_s_no
        return e_a, e_no, e_a - e_no

    def solve_stratum_baselines(causal_s: float, causal_c: float) -> Tuple[float, float]:
        p_c_a = (w_c * p_a_given_c) / p_aria_2026
        p_s_a = 1.0 - p_c_a
        p_c_no = (w_c * (1.0 - p_a_given_c)) / (1.0 - p_aria_2026)
        p_s_no = 1.0 - p_c_no
        rhs1 = e_aria_2026 - (p_c_a * causal_c + p_s_a * causal_s)
        rhs2 = e_noaria_2026
        det = p_c_a * p_s_no - p_s_a * p_c_no
        ec = (rhs1 * p_s_no - p_s_a * rhs2) / det
        es = (p_c_a * rhs2 - rhs1 * p_c_no) / det
        return es, ec

    # Prove existence of realistic positive stratum baselines (0 < es < ec) reproducing exact (59.1, 42.0):
    # Regime 1: Pure Simpson's paradox — ARIA strictly helpful (-2.0 errors in both strata)
    es1, ec1 = solve_stratum_baselines(-2.0, -2.0)
    ea1, eno1, gap1 = marginal_aria_gap(err_s_no=es1, err_c_no=ec1, causal_aria_delta_s=-2.0, causal_aria_delta_c=-2.0)
    assert abs(ea1 - 59.1) < 1e-9 and abs(eno1 - 42.0) < 1e-9 and abs(gap1 - 17.1) < 1e-9 and 0.0 < es1 < ec1

    # Regime 2: Complexity + direct ARIA misuse injection (+1.5 simple, +6.5 complex)
    es2, ec2 = solve_stratum_baselines(+1.5, +6.5)
    ea2, eno2, gap2 = marginal_aria_gap(err_s_no=es2, err_c_no=ec2, causal_aria_delta_s=+1.5, causal_aria_delta_c=+6.5)
    assert abs(ea2 - 59.1) < 1e-9 and abs(eno2 - 42.0) < 1e-9 and abs(gap2 - 17.1) < 1e-9 and 0.0 < es2 < ec2

    print(
        f"  WCAG 2.2 active SCs: {wcag22_active_total} (A+AA={wcag22_active_aa}) | "
        f"axe-core v4.14.1: {sum(axe_rule_catalog.values())} rules (WCAG 2.0: 17 fail, 34 fail+rev, 9 rev) -> "
        f"{axe_sc_default_aa}/{wcag22_active_aa} ({100*sc_share:.1f}%) default, "
        f"{axe_sc_with_22}/{wcag22_active_aa} ({100*axe_sc_with_22/wcag22_active_aa:.1f}%) w/ target-size, "
        f"{axe_sc_all_105_aa}/{wcag22_active_aa} ({100*axe_sc_all_105_aa/wcag22_active_aa:.1f}%) all"
    )
    print(
        f"  GOV.UK audit (19 cats, {tot_b} barriers): axe E/W={axe_ew}/{tot_b} ({100*axe_ew/tot_b:.1f}%), "
        f"13-tool union E/W={u_ew}/{tot_b} ({100*u_ew/tot_b:.1f}%), E/W/M={u_ewm}/{tot_b} ({100*u_ewm/tot_b:.1f}%) | "
        f"axe blind spots: Keyboard={kb_row[2]}/{kb_row[1]} (6.3%), Images={img_row[2]}/{img_row[1]} (10.0%)"
    )
    print(
        f"  Deque axe-core volume ({deque_auto_vol*100:.2f}% auto, {deque_non_auto_vol*100:.2f}% non-auto, "
        f"{deque_igt_vol*100:.2f}% w/ IGTs) vs. 20/55 ({100*sc_share:.1f}%) touched SCs "
        f"(requires r_auto>=0.5738, >= {min_concentration:.2f}x density):"
    )
    for r_auto, v_touched, w20, u35, conc in reconcil_rows:
        print(
            f"    r_auto={r_auto:.2f} -> V_touched(20 SCs)={v_touched*100:5.2f}% ({conc:.2f}x) | "
            f"42.62% non-auto = {w20*100:5.2f}% within-20 partial misses + {u35*100:5.2f}% uncovered-35 SCs"
        )
    print(
        f"  WebAIM 2026 (WAVE, separate engine/pop): 56.1 mean detected errs/page, 96% in 6 WAVE failure classes; "
        f"ARIA conservation: 0.827*59.1 + 0.173*42.0 = {weighted_2026:.2f}"
    )
    print(
        f"  A11yn cross-oracle check (WVS 1/2/3/4 exact): IR_AChecker drops {base_ir_ach:.2f}->{a11yn_ir_ach:.2f} "
        f"(-{ach_reduction_pct:.1f}%, beating GPT-5.1 0.35 / Gemini 3 Pro 0.51 / Claude Sonnet 4.6 0.57), "
        f"yet IR_AChecker/IR_Axe widens {base_ratio:.2f}x->{a11yn_ratio:.2f}x ({a11yn_ratio/base_ratio:.2f}x spike)"
    )
    print(
        f"  Simpson's-paradox feasibility witness (avg {avg_elems:.0f} DOM elems -> exact E[err|A]=59.1, E[err|~A]=42.0, gap=+17.1):"
    )
    print(
        f"    Regime 1 (helpful ARIA -2.0/-2.0): solved positive baselines es={es1:.2f}, ec={ec1:.2f} -> gap={gap1:+.1f}"
    )
    print(
        f"    Regime 2 (causal misuse +1.5/+6.5): solved positive baselines es={es2:.2f}, ec={ec2:.2f} -> gap={gap2:+.1f}"
    )


# ============================================================================
# PROBE 5: Multi-Viewport Responsive DOM Geometry & WCAG 2.2 Contrast Oracle
# ============================================================================


def wcag22_relative_luminance(rgb: Tuple[int, int, int]) -> float:
    """Exact W3C WCAG 2.2 relative luminance (0.04045 sRGB threshold)."""
    def chan(v: int) -> float:
        s = v / 255.0
        return s / 12.92 if s <= 0.04045 else ((s + 0.055) / 1.055) ** 2.4

    r, g, b = chan(rgb[0]), chan(rgb[1]), chan(rgb[2])
    return 0.2126 * r + 0.7152 * g + 0.0722 * b


def wcag22_contrast_ratio(fg: Tuple[int, int, int], bg: Tuple[int, int, int]) -> float:
    """Exact W3C WCAG 2.2 contrast ratio (L1 + 0.05) / (L2 + 0.05)."""
    l1 = wcag22_relative_luminance(fg)
    l2 = wcag22_relative_luminance(bg)
    hi, lo = (l1, l2) if l1 >= l2 else (l2, l1)
    return (hi + 0.05) / (lo + 0.05)


@dataclass(frozen=True)
class UiElement:
    elem_id: str
    tag: str
    text: str
    x: float
    y: float
    w: float
    h: float
    fg: Tuple[int, int, int]
    bg: Tuple[int, int, int]
    font_px: float = 16.0
    interactive: bool = False
    intrinsic_ar: float = 0.0  # > 0 for images


def evaluate_viewport_oracle(
    elements: Sequence[UiElement],
    viewport_w: float,
    has_viewport_meta: bool,
    is_mobile: bool,
) -> Dict[str, object]:
    """Physically coherent WebCompat/XCompat + WCAG 2.2 layout & contrast oracle.

    On mobile without <meta name="viewport">, browsers establish a 980 CSS px layout
    viewport and zoom it down by scale = viewport_w / 980.0 (Class A1.1 shrink-to-fit):
    horizontal overflow is measured against layout_viewport_w (980px), whereas effective
    rendered font size and touch-target dimensions scale by `scale`. With viewport meta
    present, layout_viewport_w == viewport_w and scale == 1.0.
    """
    layout_viewport_w = 980.0 if (is_mobile and not has_viewport_meta) else viewport_w
    scale = min(1.0, viewport_w / layout_viewport_w)

    shrink_violations = []
    overflow_violations = []
    overlap_violations = []
    img_distortion_violations = []
    target_size_violations = []
    contrast_violations = []

    for el in elements:
        eff_font = el.font_px * scale
        if el.text and eff_font < 12.0:
            shrink_violations.append((el.elem_id, round(eff_font, 2)))
        if el.x + el.w > layout_viewport_w + 1e-6 or el.x < -1e-6:
            overflow_violations.append((el.elem_id, round(max(0.0, el.x + el.w - layout_viewport_w, -el.x), 1)))
        if el.intrinsic_ar > 0.0 and el.h > 0.0:
            rendered_ar = el.w / el.h
            rel_err = abs(rendered_ar / el.intrinsic_ar - 1.0)
            if rel_err > 0.15:
                img_distortion_violations.append((el.elem_id, round(rel_err, 3)))
        if el.interactive:
            # WCAG 2.2 SC 2.5.8 Target Size (Minimum): 24x24 CSS px
            eff_w, eff_h = el.w * scale, el.h * scale
            if min(eff_w, eff_h) < 24.0:
                target_size_violations.append((el.elem_id, round(eff_w, 1), round(eff_h, 1)))
        if el.text:
            cr = wcag22_contrast_ratio(el.fg, el.bg)
            # WCAG 2.2 SC 1.4.3 normal text AA minimum 4.5:1
            if cr < 4.5:
                contrast_violations.append((el.elem_id, round(cr, 2)))

    # Pairwise sibling bounding-box overlap (Class A2.2)
    for i in range(len(elements)):
        a = elements[i]
        for j in range(i + 1, len(elements)):
            b = elements[j]
            ix = max(0.0, min(a.x + a.w, b.x + b.w) - max(a.x, b.x))
            iy = max(0.0, min(a.y + a.h, b.y + b.h) - max(a.y, b.y))
            if ix * iy > 1e-6:
                overlap_violations.append((a.elem_id, b.elem_id, round(ix * iy, 1)))

    total_v = (
        len(shrink_violations)
        + len(overflow_violations)
        + len(overlap_violations)
        + len(img_distortion_violations)
        + len(target_size_violations)
        + len(contrast_violations)
    )
    return {
        "layout_viewport_w": layout_viewport_w,
        "scale": scale,
        "total_violations": total_v,
        "shrink_a11": shrink_violations,
        "overflow_a21": overflow_violations,
        "overlap_a22": overlap_violations,
        "img_distort_b1": img_distortion_violations,
        "target_sc258": target_size_violations,
        "contrast_sc143": contrast_violations,
    }


def run_probe_5() -> None:
    print("\n========================================================================")
    print("PROBE 5: Multi-Viewport Responsive DOM Geometry & WCAG 2.2 Contrast Oracle")
    print("Provenance: [exact normative WCAG 2.2 calculation] + [controlled simulation]")
    print("========================================================================")

    # 5A. Viewport-independent WCAG 2.2 contrast threshold vs. perceptual color similarity
    cr_bw = wcag22_contrast_ratio((0, 0, 0), (255, 255, 255))
    cr_76 = wcag22_contrast_ratio((0x76, 0x76, 0x76), (255, 255, 255))
    cr_77 = wcag22_contrast_ratio((0x77, 0x77, 0x77), (255, 255, 255))
    cr_88 = wcag22_contrast_ratio((0x88, 0x88, 0x88), (255, 255, 255))
    de00_76_88 = ciede2000(srgb_to_lab((0x76, 0x76, 0x76)), srgb_to_lab((0x88, 0x88, 0x88)))
    d2c_col_76_88 = max(0.0, 1.0 - de00_76_88 / 100.0)
    assert abs(cr_bw - 21.0) < 1e-9
    assert cr_76 >= 4.5 and cr_77 < 4.5 and cr_88 < 4.5
    assert d2c_col_76_88 > 0.92  # Perceptually close yet fails normative WCAG 2.2 SC 1.4.3

    # 5B. Genuine Desktop 1280x800 Reference vs. Distinct Generated Candidate (never f(x, x))
    desktop_elems_ref = (
        UiElement("hero_title", "h1", "cloud analytics suite", 80, 40, 640, 48, (17, 24, 39), (255, 255, 255), 32.0),
        UiElement("cta_btn", "button", "start trial", 80, 120, 140, 40, (255, 255, 255), (29, 78, 216), 16.0, interactive=True),
        UiElement("nav_card", "p", "real-time telemetry dashboard", 80, 240, 960, 40, (55, 65, 81), (255, 255, 255), 16.0),
        UiElement("hero_img", "img", "", 760, 40, 320, 180, (0, 0, 0), (255, 255, 255), intrinsic_ar=16.0 / 9.0),
    )
    # Distinct generated desktop candidate (realistic 2-4px layout offset, compliant colors)
    desktop_elems_cand = (
        UiElement("hero_title", "h1", "cloud analytics suite", 84, 42, 636, 48, (17, 24, 39), (255, 255, 255), 32.0),
        UiElement("cta_btn", "button", "start trial", 84, 122, 142, 40, (255, 255, 255), (29, 78, 216), 16.0, interactive=True),
        UiElement("nav_card", "p", "real-time telemetry dashboard", 84, 242, 956, 40, (55, 65, 81), (255, 255, 255), 16.0),
        UiElement("hero_img", "img", "", 764, 42, 320, 180, (0, 0, 0), (255, 255, 255), intrinsic_ar=16.0 / 9.0),
    )
    assert desktop_elems_cand != desktop_elems_ref

    # 5C. Mobile Case A (390x844, has_viewport_meta=False -> 980px layout viewport, scale=0.398):
    # Physically consistent: elements fit inside 980px (0 horizontal overflow, 0 overlap, same compliant colors),
    # yet 0.398 shrink-to-fit collapses 16px body/button fonts to 6.37px (<12px) and 140x40 CTA to 55.7x15.9px (<24px).
    mobile_case_a_no_meta = (
        UiElement("hero_title", "h1", "cloud analytics suite", 16, 40, 600, 48, (17, 24, 39), (255, 255, 255), 32.0),
        UiElement("cta_btn", "button", "start trial", 16, 120, 140, 40, (255, 255, 255), (29, 78, 216), 16.0, interactive=True),
        UiElement("nav_card", "p", "real-time telemetry dashboard", 16, 240, 948, 40, (55, 65, 81), (255, 255, 255), 16.0),
        UiElement("hero_img", "img", "", 644, 40, 320, 180, (0, 0, 0), (255, 255, 255), intrinsic_ar=16.0 / 9.0),
    )

    # 5D. Mobile Case B (390x844, has_viewport_meta=True -> 390px layout viewport, scale=1.000):
    # Physically consistent: viewport meta is present (0 shrink_A1.1, same compliant colors),
    # yet fixed-width 960px nav_card overflows by 586px, overlaps cta_btn by 252px^2, stretches 16:9 hero_img
    # to 358x358 (0.438 AR error), and shrinks mobile icon button to 18x18 (<24px SC 2.5.8).
    mobile_case_b_overflow = (
        UiElement("hero_title", "h1", "cloud analytics suite", 16, 20, 358, 40, (17, 24, 39), (255, 255, 255), 24.0),
        UiElement("cta_btn", "button", "start trial", 16, 80, 18, 18, (255, 255, 255), (29, 78, 216), 14.0, interactive=True),
        UiElement("nav_card", "p", "real-time telemetry dashboard", 16, 84, 960, 36, (55, 65, 81), (255, 255, 255), 16.0),
        UiElement("hero_img", "img", "", 16, 150, 358, 358, (0, 0, 0), (255, 255, 255), intrinsic_ar=16.0 / 9.0),
    )

    # 5E. Mobile Repaired Responsive Candidate (390x844, has_viewport_meta=True, scale=1.000)
    mobile_repaired = (
        UiElement("hero_title", "h1", "cloud analytics suite", 16, 20, 358, 40, (17, 24, 39), (255, 255, 255), 24.0),
        UiElement("cta_btn", "button", "start trial", 16, 76, 140, 44, (255, 255, 255), (29, 78, 216), 16.0, interactive=True),
        UiElement("nav_card", "p", "real-time telemetry dashboard", 16, 136, 358, 44, (55, 65, 81), (255, 255, 255), 16.0),
        UiElement("hero_img", "img", "", 16, 196, 358, 201, (0, 0, 0), (255, 255, 255), intrinsic_ar=16.0 / 9.0),
    )

    def to_d2c(els: Sequence[UiElement], vw: float, vh: float) -> List[dict]:
        return [
            {"tag": e.tag, "text": e.text, "bbox": (e.x / vw, e.y / vh, e.w / vw, e.h / vh), "color": e.fg}
            for e in els
            if e.text
        ]

    d2c_desktop = d2c_evaluate_blocks(to_d2c(desktop_elems_cand, 1280, 800), to_d2c(desktop_elems_ref, 1280, 800))
    ora_desk = evaluate_viewport_oracle(desktop_elems_cand, 1280.0, has_viewport_meta=False, is_mobile=False)
    ora_mob_a = evaluate_viewport_oracle(mobile_case_a_no_meta, 390.0, has_viewport_meta=False, is_mobile=True)
    ora_mob_b = evaluate_viewport_oracle(mobile_case_b_overflow, 390.0, has_viewport_meta=True, is_mobile=True)
    ora_mob_rep = evaluate_viewport_oracle(mobile_repaired, 390.0, has_viewport_meta=True, is_mobile=True)

    assert d2c_desktop["block"] == 1.0 and d2c_desktop["text"] == 1.0
    assert 0.99 < d2c_desktop["position"] < 1.0 and d2c_desktop["color"] == 1.0
    assert ora_desk["total_violations"] == 0

    # Case A: missing viewport meta -> shrink_A1.1 + scaled target_SC2.5.8 ONLY (0 overflow, 0 contrast)
    assert ora_mob_a["layout_viewport_w"] == 980.0
    assert len(ora_mob_a["shrink_a11"]) == 2
    assert len(ora_mob_a["target_sc258"]) == 1
    assert len(ora_mob_a["overflow_a21"]) == 0
    assert len(ora_mob_a["overlap_a22"]) == 0
    assert len(ora_mob_a["img_distort_b1"]) == 0
    assert len(ora_mob_a["contrast_sc143"]) == 0
    assert ora_mob_a["total_violations"] == 3

    # Case B: viewport meta present -> overflow + overlap + img_distortion + unscaled target_SC2.5.8 (0 shrink, 0 contrast)
    assert ora_mob_b["layout_viewport_w"] == 390.0
    assert len(ora_mob_b["shrink_a11"]) == 0
    assert len(ora_mob_b["overflow_a21"]) == 1 and ora_mob_b["overflow_a21"][0][1] == 586.0
    assert len(ora_mob_b["overlap_a22"]) == 1 and ora_mob_b["overlap_a22"][0][2] == 252.0
    assert len(ora_mob_b["img_distort_b1"]) == 1 and ora_mob_b["img_distort_b1"][0][1] == 0.438
    assert len(ora_mob_b["target_sc258"]) == 1 and ora_mob_b["target_sc258"][0][1:] == (18.0, 18.0)
    assert len(ora_mob_b["contrast_sc143"]) == 0
    assert ora_mob_b["total_violations"] == 4

    assert ora_mob_rep["total_violations"] == 0

    print(
        f"  WCAG 2.2 contrast oracle (viewport-independent): #000/#fff={cr_bw:.2f}:1 | "
        f"#767676/#fff={cr_76:.2f}:1 (AA PASS) | #777777/#fff={cr_77:.2f}:1 (AA FAIL) | "
        f"#888888/#fff={cr_88:.2f}:1 (AA FAIL, yet D2C color_sim vs #767676={d2c_col_76_88:.4f})"
    )
    print(
        f"  Desktop (1280x800, distinct cand vs ref): D2C Block={d2c_desktop['block']:.4f} "
        f"Pos={d2c_desktop['position']:.4f} Color={d2c_desktop['color']:.4f} | Desktop DOM oracle violations={ora_desk['total_violations']}"
    )
    print(
        f"  Mobile Case A (390x844, no viewport meta -> layout={ora_mob_a['layout_viewport_w']:.0f}px, scale={ora_mob_a['scale']:.3f}): "
        f"total={ora_mob_a['total_violations']} -> shrink_A1.1={ora_mob_a['shrink_a11']}, "
        f"target_SC2.5.8={ora_mob_a['target_sc258']}, overflow_A2.1={len(ora_mob_a['overflow_a21'])}"
    )
    print(
        f"  Mobile Case B (390x844, viewport meta present -> layout={ora_mob_b['layout_viewport_w']:.0f}px, scale={ora_mob_b['scale']:.3f}): "
        f"total={ora_mob_b['total_violations']} -> overflow_A2.1={ora_mob_b['overflow_a21']}, "
        f"overlap_A2.2={ora_mob_b['overlap_a22']}, img_B1={ora_mob_b['img_distort_b1']}, "
        f"target_SC2.5.8={ora_mob_b['target_sc258']}, shrink_A1.1={len(ora_mob_b['shrink_a11'])}"
    )
    print(
        f"  Mobile Repaired (390x844, viewport meta present, scale={ora_mob_rep['scale']:.3f}): "
        f"total_violations={ora_mob_rep['total_violations']} (ALL desktop + mobile + WCAG 2.2 invariants PASS)"
    )


def main() -> None:
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    run_probe_5()
    print("\nALL 5 PROBES PASSED NON-VACUOUS INVARIANTS.")


if __name__ == "__main__":
    main()
