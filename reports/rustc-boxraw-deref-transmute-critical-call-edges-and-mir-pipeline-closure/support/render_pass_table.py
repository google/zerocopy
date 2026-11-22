#!/usr/bin/env python3
"""Render the pass-order table of one `pass_pipeline_rustc_<commit>.json` as Markdown, and
(optionally) compare a probe's observed dump sequence with the source order.

    python3 render_pass_table.py pass_pipeline_rustc_bdf712ee.json > table.md
    python3 render_pass_table.py pass_pipeline_rustc_14210df0e.json \
        --compare-probe probe_results_rustc_14210df0e.json

The "Miri default" column is DERIVED: it evaluates each pass's policy expression under the
MIR-affecting flags Miri passes by default (`-Zmir-opt-level=0 -Zmir-preserve-ub
-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums,-ReferencePropagation,-GVN`) with every
other option at its default and an unwinding panic strategy. Conditions this script does not know
how to evaluate are rendered as `?` rather than guessed.

Standard library only (Python 3.10+).
"""
from __future__ import annotations

import argparse
import json
import re
import sys

MIRI_DISABLED = {"CheckAlignment", "CheckNull", "CheckEnums", "ReferencePropagation", "GVN"}

# condition text (as it appears in `PassPolicy::optional(<cond>)` or `is_enabled`) -> value under
# Miri's default flags, and a short human rendering.
COND = {
    "ctx.ub_checks()": (False, "`ub_checks()`"),
    "sess.ub_checks()": (False, "`ub_checks()`"),
    "ctx.instrument_coverage()": (False, "`-Cinstrument-coverage`"),
    "sess.instrument_coverage()": (False, "`-Cinstrument-coverage`"),
    "ctx.panic_strategy().unwinds()": (True, "panic strategy unwinds"),
    "sess.panic_strategy().unwinds()": (True, "panic strategy unwinds"),
    "!ctx.opts.unstable_opts.mir_preserve_ub": (False, "not `-Zmir-preserve-ub`"),
    "!sess.opts.unstable_opts.mir_preserve_ub": (False, "not `-Zmir-preserve-ub`"),
    "ctx.opts.unstable_opts.mir_strip_debuginfo != MirStripDebugInfo::None":
        (False, "`-Zmir-strip-debuginfo` set"),
    "sess.opts.unstable_opts.mir_strip_debuginfo != MirStripDebugInfo::None":
        (False, "`-Zmir-strip-debuginfo` set"),
    "!ctx.emit_lifetime_markers()": (True, "no lifetime markers"),
    "!sess.emit_lifetime_markers()": (True, "no lifetime markers"),
    "!ctx.target.is_like_gpu": (True, "target is not GPU-like"),
    "!sess.target.is_like_gpu": (True, "target is not GPU-like"),
    "!ctx.opts.unstable_opts.mir_move_elimination": (True, "not `-Zmir-move-elimination`"),
    "ctx.opts.unstable_opts.mir_move_elimination": (False, "`-Zmir-move-elimination`"),
    "true": (True, ""),
    "false": (False, ""),
}


def phase_short(p):
    if p in (None, "None"):
        return "none"
    m = re.search(r"MirPhase::(\w+)\((?:\w+)::(\w+)\)", p)
    return f"`{m.group(1)}({m.group(2)})`" if m else p


def policy_cell(e):
    c = e.get("classification") or {}
    pol = e.get("policy") or {}
    kind = c.get("kind")
    lvl = c.get("min_mir_opt_level")
    other = c.get("other_conditions")
    conds = []
    under_miri = True
    if kind == "Required" or kind == "is_required=true" and "is_enabled" not in pol:
        label = "Required" if kind == "Required" else "`is_required` = true"
        return label, "always", "on", "R"
    if kind and kind.startswith("is_required="):
        label = f"`is_required` = {kind.split('=')[1]}"
    else:
        label = "Optional"
    name = e["type"]
    if name == "Inline":
        return label, "level 2 with `-C opt-level` 2/3 and no incremental; level >= 3; or `-Zinline-mir`", "off", "O"
    if lvl is not None:
        conds.append(f"level >= {lvl}")
        under_miri = under_miri and lvl == 0
    if other:
        for part in [x.strip() for x in other.split("&&")]:
            if part in COND:
                val, txt = COND[part]
                if txt:
                    conds.append(txt)
                under_miri = under_miri and val
            else:
                conds.append(f"`{part}`")
                under_miri = None if under_miri else under_miri
    default = c.get("default")
    if default == "off":
        conds.append("off unless `-Zmir-enable-passes=+…`")
        under_miri = False
    if name in MIRI_DISABLED:
        under_miri = False
    when = "; ".join(conds) if conds else "always (unless `-Zmir-enable-passes=-…`)"
    miri = "?" if under_miri is None else ("on" if under_miri else "off")
    return label, when, miri, ("L" if e.get("wrapper") == "Lint" else "O")


def render(doc):
    out = []
    lib_lists = [l for l in doc["lists"] if l["file"] == "lib.rs"]
    n = 0
    for l in lib_lists:
        call = l["pass_manager_call"]
        out.append(f"\n**`{l['enclosing_fn']}`** (`lib.rs:{l['first_line']}`), `pm::{call}`, "
                   f"phase set afterwards: {phase_short(l['phase_change_argument'])}\n")
        out.append("| # | `lib.rs` line | Pass | Policy | Enabled by default when | Miri default | Class |")
        out.append("|---|---|---|---|---|---|---|")
        for e in l["entries"]:
            n += 1
            nm = e["type"] + (f"::{e['variant']}" if e.get("variant") else "")
            if e.get("wrapper") == "Lint":
                nm = f"Lint({nm})"
            elif e.get("wrapper") == "o1":
                nm = f"o1({nm})"
            label, when, miri, cls = policy_cell(e)
            out.append(f"| {n} | {e['line']} | `{nm}` | {label} | {when} | {miri} | {cls} |")
    return "\n".join(out) + "\n", n


def dump_name(e):
    """The name a pass uses for its MIR dump files: the type name, plus the variant in
    kebab-case for the enum-valued passes that override `name()`."""
    return e["type"]


def compare(doc, probe):
    """Is each observed dump sequence a subsequence of the source order?"""
    order = []
    for l in doc["lists"]:
        if l["file"] != "lib.rs" or l["enclosing_fn"] in ("inner_mir_for_ctfe",):
            continue
        if l["enclosing_fn"] == "run_analysis_to_runtime_passes":
            continue  # only with const_precise_live_drops checking enabled
        for e in l["entries"]:
            if e.get("wrapper") == "Lint":
                continue  # lints do not dump
            order.append(e["type"])
    phase_markers = {"built", "analysis", "analysis-post-cleanup", "runtime", "runtime-post-cleanup",
                     "runtime-optimized"}
    res = {}
    for tag, seq in probe["dump_sequences_crit_call"].items():
        observed = [t.split(".", 1)[1].split("-")[0] for t in seq
                    if t.split(".", 1)[1] not in phase_markers]
        i = 0
        missing = []
        for name in observed:
            j = i
            while j < len(order) and order[j] != name:
                j += 1
            if j == len(order):
                missing.append(name)
            else:
                i = j + 1
        res[tag] = {"observed_pass_dumps": len(observed), "is_subsequence_of_source_order": not missing,
                    "not_matched_in_order": missing}
    return res


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("pipeline_json")
    ap.add_argument("--compare-probe", default=None)
    args = ap.parse_args()
    with open(args.pipeline_json, encoding="utf-8") as f:
        doc = json.load(f)
    if args.compare_probe:
        with open(args.compare_probe, encoding="utf-8") as f:
            probe = json.load(f)
        res = compare(doc, probe)
        print(json.dumps({"pipeline_commit": doc["commit"],
                          "probe_commit": probe["toolchain"].get("commit-hash"), "result": res},
                         indent=1, sort_keys=True))
        return 0 if all(v["is_subsequence_of_source_order"] for v in res.values()) else 1
    text, n = render(doc)
    sys.stdout.write(f"<!-- generated from {args.pipeline_json}: {n} entries -->\n" + text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
