#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Verify Silesia benchmark integrity, aggregate vs. geometric-mean bias,
convex-hull Pareto dominance under harmonic time-sharing, and length-only
verification blind spots.

Run:
  python3 verify_benchmarks_and_pareto.py
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import subprocess
import zlib

HERE = Path(__file__).resolve().parent
DATASET_PATH = HERE / "silesia_2mib_single_core.json"

SILESIA_MANIFEST = {
    "dickens": (10192446, "b24c37886142e11d0ee687db6ab06f936207aa7f2ea1fd1d9a36763c7a507e6a"),
    "mozilla": (51220480, "657fc3764b0c75ac9de9623125705831ebbfbe08fed248df73bc2dc66e2a963b"),
    "mr": (9970564, "68637ed52e3e4860174ed2dc0840ac77d5f1a60abbcb13770d5754e3774d53e6"),
    "nci": (33553445, "fc63a31770947b8c2062d3b19ca94c00485a232bb91b502021948fee983e1635"),
    "ooffice": (6152192, "e7ee013880d34dd5208283d0d3d91b07f442e067454276095ded14f322a656eb"),
    "osdb": (10085684, "60f027179302ca3ad87c58ac90b6be72ec23588aaa7a3b7fe8ecc0f11def3fa3"),
    "reymont": (6627202, "0eac0114a3dfe6e2ee1f345a0f79d653cb26c3bc9f0ed79238af4933422b7578"),
    "samba": (21606400, "93ba07bc44d8267789c1d911992f40b089ffa2140b4a160fac11ccae9a40e7b2"),
    "sao": (7251944, "c2d0ea2cc59d4c21b7fe43a71499342a00cbe530a1d5548770e91ecd6214adcc"),
    "webster": (41458703, "6a68f69b26daf09f9dd84f7470368553194a0b294fcfa80f1604efb11143a383"),
    "x-ray": (8474240, "7de9fce1405dc44ae5e6813ed21cd5751e761bd4265655a005d39b9685d1c9ad"),
    "xml": (5345280, "0e82e54e695c1938e4193448022543845b33020c8be6bf3bf3ead2224903e08c"),
}


def geomean(vals: list[float]) -> float:
    return math.exp(sum(math.log(v) for v in vals) / len(vals))


def harmonic_hull_eval(points: list[tuple[int, float, float]], target_ratio: float) -> dict | None:
    """Compute tightest upper-frontier throughput at `ratio <= target_ratio` via
    pointwise dominance or time-sharing between two levels (`1/v` convexity).
    """
    pts = sorted(points, key=lambda x: x[1])
    inv_pts = [(lvl, r, 1.0 / v, v) for lvl, r, v in pts]
    best = None
    for i in range(len(inv_pts)):
        l0, r0, s0, v0 = inv_pts[i]
        if r0 <= target_ratio + 1e-12:
            if best is None or s0 < best[0]:
                best = (s0, (l0, l0, 0.0, v0))
        for j in range(i + 1, len(inv_pts)):
            l1, r1, s1, v1 = inv_pts[j]
            # pts sorted ascending by ratio: r0 <= r1 (`l0` tighter, `l1` faster)
            if r0 <= target_ratio <= r1 + 1e-12 and r1 > r0:
                f = min(1.0, max(0.0, (target_ratio - r0) / (r1 - r0)))
                s_mix = f * s1 + (1.0 - f) * s0
                if best is None or s_mix < best[0]:
                    best = (s_mix, (l0, l1, f, 1.0 / s_mix))
    if best is None:
        return None
    l_tight, l_fast, f_fast, v_mix = best[1]
    return {
        "levels": (l_tight, l_fast),
        "weight_fast": round(f_fast, 4),
        "hull_comp_mibs": round(v_mix, 4),
    }


def main() -> int:
    assert sum(sz for sz, _ in SILESIA_MANIFEST.values()) == 211938580
    corpus_dir = Path("/tmp/silesia_corpus")
    corpus_live = None
    if corpus_dir.is_dir():
        for name, (exp_sz, exp_sha) in SILESIA_MANIFEST.items():
            raw = (corpus_dir / name).read_bytes()
            assert len(raw) == exp_sz, f"Size mismatch on {name}"
            assert hashlib.sha256(raw).hexdigest() == exp_sha, f"SHA-256 mismatch on {name}"
        corpus_live = len(SILESIA_MANIFEST)

    data = json.loads(DATASET_PATH.read_text())
    rows = data["rows"]
    profiles = sorted({r["profile"] for r in rows})
    assert len(rows) == 7 * 108

    summary: dict[str, dict[int, dict]] = {}
    for prof in profiles:
        summary[prof] = {}
        for lvl in range(1, 10):
            sub = [r for r in rows if r["profile"] == prof and r["level"] == lvl]
            assert len(sub) == 12
            gm_r = geomean([r["ratio"] for r in sub])
            agg_r = sum(r["out_size"] for r in sub) / sum(r["size"] for r in sub)
            gm_c = geomean([r["compress_mibs"] for r in sub])
            gm_d = geomean([r["decompress_mibs"] for r in sub])
            summary[prof][lvl] = {
                "gm_ratio": round(gm_r, 6),
                "agg_ratio": round(agg_r, 6),
                "agg_minus_gm_pp": round((agg_r - gm_r) * 100.0, 2),
                "comp_mibs": round(gm_c, 2),
                "decomp_mibs": round(gm_d, 2),
            }

    # Check pointwise vs convex-hull dominance against lean_zip_2f7a63f
    lz_curve = {lvl: summary["lean_zip_2f7a63f"][lvl] for lvl in range(1, 10)}
    dominance_vs_lean_zip = {}
    for prof in profiles:
        if prof == "lean_zip_2f7a63f":
            continue
        p_pts = [
            (lvl, summary[prof][lvl]["gm_ratio"], summary[prof][lvl]["comp_mibs"])
            for lvl in range(1, 10)
        ]
        pointwise_fails = []
        hull_gaps = {}
        for lvl in range(1, 10):
            lz_r = lz_curve[lvl]["gm_ratio"]
            lz_c = lz_curve[lvl]["comp_mibs"]
            if not (summary[prof][lvl]["gm_ratio"] <= lz_r and summary[prof][lvl]["comp_mibs"] >= lz_c):
                pointwise_fails.append(lvl)
            hull = harmonic_hull_eval(p_pts, lz_r)
            hull_gaps[lvl] = hull
            if prof != "miniz_oxide_0_9_1" and prof != "zlib_1_3_2":
                assert hull is not None and hull["hull_comp_mibs"] > lz_c, (
                    f"{prof} failed hull dominance at L{lvl}: {hull} vs lean_zip {lz_c}"
                )
        dominance_vs_lean_zip[prof] = {
            "pointwise_fails": pointwise_fails,
            "L8_hull": hull_gaps[8],
            "L9_hull": hull_gaps[9],
        }

    # Per-file compressed size wins (zlib vs lean-zip across 108 pairs)
    lz_map = {(r["file"], r["level"]): r["out_size"] for r in rows if r["profile"] == "lean_zip_2f7a63f"}
    zlib_map = {(r["file"], r["level"]): r["out_size"] for r in rows if r["profile"] == "zlib_1_3_2"}
    zlib_smaller_than_lz = sum(1 for k in lz_map if zlib_map[k] < lz_map[k])

    # Verify length-only validation blind spot: two unequal streams decode to identical size
    payload_a = b"DEFLATE_VERIFY_ORIGINAL_PAYLOAD_" * 128
    payload_b = b"DEFLATE_CORRUPTED_SILENT_BYTE!!!" * 128
    assert len(payload_a) == len(payload_b)
    comp_b = zlib.compress(payload_b)[2:-4]
    dec_b = zlib.decompress(comp_b, wbits=-15)
    assert len(dec_b) == len(payload_a) and dec_b != payload_a

    # Optional live C IR inspection if /tmp/lean-zip build outputs exist
    lean_zip_ir_stats = None
    lz_ir = Path("/tmp/lean-zip/.lake/build/ir")
    if lz_ir.is_dir():
        c_files = list(lz_ir.rglob("*.c"))
        tot_bytes = sum(p.stat().st_size for p in c_files)
        wide_c = lz_ir / "Zip/Native/Wide.c"
        wide_bytes = wide_c.stat().st_size if wide_c.is_file() else 0
        is_excl = sum(p.read_text(errors="ignore").count("lean_is_exclusive") for p in c_files)
        nat_ops = sum(
            sum(
                p.read_text(errors="ignore").count(tok)
                for tok in [
                    "lean_nat_add", "lean_nat_sub", "lean_nat_mul", "lean_nat_div",
                    "lean_nat_mod", "lean_nat_dec_lt", "lean_nat_dec_le", "lean_nat_dec_eq",
                    "lean_nat_lor", "lean_nat_land", "lean_nat_shiftl", "lean_nat_shiftr",
                ]
            )
            for p in c_files
        )
        max_str_len = None
        bs_bin = Path("/tmp/lean-zip/.lake/build/bin/bench_silesia")
        if bs_bin.is_file():
            out_s = subprocess.getoutput(
                f"strings {bs_bin} | awk '{{print length}}' | sort -nr | head -n 1"
            ).strip()
            max_str_len = int(out_s) if out_s.isdigit() else None
        lean_zip_ir_stats = {
            "c_files": len(c_files),
            "total_c_bytes": tot_bytes,
            "wide_c_bytes": wide_bytes,
            "lean_is_exclusive_count": is_excl,
            "boxed_lean_nat_ops": nat_ops,
            "elf_bytes": bs_bin.stat().st_size if bs_bin.is_file() else None,
            "max_elf_string_bytes": max_str_len,
        }

    print(
        json.dumps(
            {
                "status": "PASS",
                "corpus_total_bytes": 211938580,
                "corpus_live_verified_files": corpus_live,
                "row_count": len(rows),
                "headline_levels": {
                    prof: {str(lv): summary[prof][lv] for lv in (1, 6, 8, 9)}
                    for prof in profiles
                },
                "dominance_vs_lean_zip": dominance_vs_lean_zip,
                "zlib_smaller_than_lean_zip_of_108": zlib_smaller_than_lz,
                "length_only_blind_spot_verified": True,
                "lean_zip_ir_stats": lean_zip_ir_stats,
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
