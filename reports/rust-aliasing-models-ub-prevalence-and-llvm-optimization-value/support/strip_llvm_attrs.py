#!/usr/bin/env python3
"""Deterministic LLVM IR attribute & metadata stripper for aliasing/value-fact ablation (S7)."""
import argparse
import json
import re
from pathlib import Path

MODES = [
    "Baseline_Full",
    "No_Mut_NoAlias",
    "No_Shared_NoAlias_Readonly",
    "No_Box_NoAlias",
    "No_Dereferenceable",
    "No_Noundef",
    "No_Captures_NoCapture",
    "No_Range_Nonnull_Metadata",
    "Strip_All_Alias_And_Value_Facts",
]

def strip_param_segment(seg: str, mode: str, counts: dict) -> str:
    if not seg.strip().startswith("ptr"):
        if mode in ("No_Noundef", "Strip_All_Alias_And_Value_Facts") and "noundef" in seg:
            counts["noundef_stripped"] += seg.count("noundef")
            seg = re.sub(r"\bnoundef\s*", "", seg)
        if mode in ("No_Range_Nonnull_Metadata", "Strip_All_Alias_And_Value_Facts") and "range(" in seg:
            counts["range_nonnull_stripped"] += 1
            seg = re.sub(r"\brange\([^)]*\)\s*", "", seg)
        return seg

    is_readonly = bool(re.search(r"\breadonly\b", seg))
    if mode in ("No_Mut_NoAlias", "Strip_All_Alias_And_Value_Facts") and not is_readonly:
        if re.search(r"\bnoalias\b", seg):
            counts["noalias_mut_stripped"] += 1
            seg = re.sub(r"\bnoalias\s*", "", seg)
    if mode in ("No_Shared_NoAlias_Readonly", "Strip_All_Alias_And_Value_Facts") and is_readonly:
        if re.search(r"\bnoalias\b", seg):
            counts["noalias_shared_stripped"] += 1
            seg = re.sub(r"\bnoalias\s*", "", seg)
        if re.search(r"\breadonly\b", seg):
            counts["readonly_stripped"] += 1
            seg = re.sub(r"\breadonly\s*", "", seg)
    if mode in ("No_Dereferenceable", "Strip_All_Alias_And_Value_Facts"):
        n_d = len(re.findall(r"\bdereferenceable(?:_or_null)?\(\d+\)", seg))
        if n_d:
            counts["dereferenceable_stripped"] += n_d
            seg = re.sub(r"\bdereferenceable(?:_or_null)?\(\d+\)\s*", "", seg)
    if mode in ("No_Noundef", "Strip_All_Alias_And_Value_Facts"):
        if re.search(r"\bnoundef\b", seg):
            counts["noundef_stripped"] += 1
            seg = re.sub(r"\bnoundef\s*", "", seg)
    if mode in ("No_Captures_NoCapture", "Strip_All_Alias_And_Value_Facts"):
        if re.search(r"\b(?:nocapture|captures\([^)]*\))", seg):
            counts["nocapture_stripped"] += 1
            seg = re.sub(r"\b(?:nocapture|captures\([^)]*\))\s*", "", seg)
    if mode in ("No_Range_Nonnull_Metadata", "Strip_All_Alias_And_Value_Facts"):
        if re.search(r"\bnonnull\b", seg):
            counts["range_nonnull_stripped"] += 1
            seg = re.sub(r"\bnonnull\s*", "", seg)
    return seg

def split_top_level_commas(param_str: str) -> list[str]:
    parts = []
    depth = 0
    cur = []
    for ch in param_str:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            parts.append("".join(cur))
            cur = []
            continue
        cur.append(ch)
    if cur:
        parts.append("".join(cur))
    return parts

def strip_ir(ir_text: str, mode: str) -> tuple[str, dict]:
    counts = {
        "noalias_mut_stripped": 0,
        "noalias_shared_stripped": 0,
        "readonly_stripped": 0,
        "dereferenceable_stripped": 0,
        "noundef_stripped": 0,
        "nocapture_stripped": 0,
        "range_nonnull_stripped": 0,
    }
    if mode == "Baseline_Full" or mode == "No_Box_NoAlias":
        return ir_text, counts

    out_lines = []
    for line in ir_text.splitlines():
        if line.startswith("define ") or line.startswith("declare "):
            m = re.match(r'^((?:define|declare)\s+.*?@[A-Za-z0-9_.$"]+\()(.*)(\)\s*(?:unnamed_addr|#[0-9]+|!guid|\{).*)$', line)
            if m:
                prefix, params, suffix = m.group(1), m.group(2), m.group(3)
                if mode in ("No_Noundef", "Strip_All_Alias_And_Value_Facts") and "noundef" in prefix:
                    counts["noundef_stripped"] += 1
                    prefix = re.sub(r"\bnoundef\s*", "", prefix)
                segs = split_top_level_commas(params)
                new_segs = [strip_param_segment(s.strip(), mode, counts) for s in segs]
                line = prefix + ", ".join(new_segs) + suffix

        if mode in ("No_Range_Nonnull_Metadata", "Strip_All_Alias_And_Value_Facts"):
            for md in ("!range", "!nonnull", "!noundef"):
                if md in line:
                    counts["range_nonnull_stripped"] += 1
                    line = re.sub(r",\s*" + re.escape(md) + r"\s+!\d+", "", line)
        if mode in ("No_Mut_NoAlias", "No_Shared_NoAlias_Readonly", "Strip_All_Alias_And_Value_Facts"):
            for md in ("!alias.scope", "!noalias"):
                if md in line:
                    line = re.sub(r",\s*" + re.escape(md) + r"\s+!\d+", "", line)

        out_lines.append(line)
    return "\n".join(out_lines) + "\n", counts

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--input", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    ap.add_argument("--mode", required=True, choices=MODES)
    args = ap.parse_args()
    text = args.input.read_text(encoding="utf-8")
    modified, counts = strip_ir(text, args.mode)
    args.output.write_text(modified, encoding="utf-8")
    print(json.dumps({"mode": args.mode, "counts": counts}))

if __name__ == "__main__":
    main()
