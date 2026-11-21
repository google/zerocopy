#!/usr/bin/env python3
"""Probe rustc + Miri for edition-dependent temporary drop scopes and for the
`UnreachableEnumBranching` MIR pass.

Everything recorded in the output JSON is produced by running the given
`rustc` and `miri` binaries on the Rust sources in `rust/` next to this file.
The only result-like literals in this script are the *expectations* passed to
`check(...)` at the bottom of `main`; each is compared against an observed
value and the script exits non-zero if any comparison fails.

Usage:

    python3 probe_edition2024_drop_scopes_and_enum_branching.py \
        --rustc <path to nightly rustc> \
        --miri <path to the matching miri binary> \
        --miri-sysroot <sysroot built by `cargo miri setup`> \
        [--retained-receipt retained_receipt_rustc_1_102_0_nightly.json] \
        --out probe_results.json

A nightly toolchain is required (`-Zdump-mir`, `-Zmir-opt-level`). Standard
library only; needs Python 3.10+.
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUST_DIR = HERE / "rust"
SOURCES = (
    "drop_order.rs",
    "tail_temp_borrows_local.rs",
    "block_tail_temp_escapes.rs",
    "if_let_mutex_guard.rs",
    "scrutinee_value_vs_place.rs",
    "enum_branching.rs",
)
EDITIONS = ("2021", "2024")
TIMEOUT_S = 300


class Runner:
    """Runs tools inside one scratch directory and scrubs it from all output."""

    def __init__(self, rustc: str, miri: str, miri_sysroot: str, workdir: Path):
        self.rustc = rustc
        self.miri = miri
        self.miri_sysroot = miri_sysroot
        self.workdir = workdir
        self._scrub = [
            (str(workdir), "<workdir>"),
            (miri_sysroot, "<miri-sysroot>"),
            (miri, "<miri>"),
            (rustc, "<rustc>"),
            (str(Path.home()), "<home>"),
        ]

    def scrub(self, text: str) -> str:
        for needle, replacement in self._scrub:
            if needle:
                text = text.replace(needle, replacement)
        return text

    def run(self, argv: list[str]) -> dict:
        proc = subprocess.run(
            argv,
            cwd=self.workdir,
            capture_output=True,
            text=True,
            timeout=TIMEOUT_S,
            env={**os.environ, "RUSTC_BOOTSTRAP": "", "NO_COLOR": "1"},
        )
        return {
            "argv": [self.scrub(a) for a in argv],
            "rc": proc.returncode,
            "stdout": self.scrub(proc.stdout),
            "stderr": self.scrub(proc.stderr),
        }

    def rustc_run(self, args: list[str]) -> dict:
        return self.run([self.rustc, *args])

    def miri_run(self, args: list[str]) -> dict:
        return self.run([self.miri, "--sysroot", self.miri_sysroot, *args])

    def exe_run(self, name: str) -> dict:
        return self.run([str(self.workdir / name)])


def diagnostics(stderr: str) -> dict:
    """Error codes and headline `error` lines of a rustc/Miri stderr."""
    return {
        "error_codes": sorted(set(re.findall(r"error\[(E\d{4})\]", stderr))),
        "error_lines": [l for l in stderr.splitlines() if l.startswith("error")][:6],
    }


def compact(result: dict) -> dict:
    """A result without the full stderr (kept only as diagnostics)."""
    return {
        "argv": result["argv"],
        "rc": result["rc"],
        "stdout": result["stdout"],
        **diagnostics(result["stderr"]),
    }


# --------------------------------------------------------------------------
# MIR text helpers
# --------------------------------------------------------------------------

BLOCK_RE = re.compile(r"^ {4}(bb\d+)( \(cleanup\))?: \{$")


def parse_mir_blocks(text: str) -> dict:
    blocks: dict[str, dict] = {}
    current = None
    for line in text.splitlines():
        m = BLOCK_RE.match(line)
        if m:
            current = m.group(1)
            blocks[current] = {"cleanup": bool(m.group(2)), "lines": []}
            continue
        if current is not None:
            if line.strip() == "}":
                current = None
            elif line.strip():
                blocks[current]["lines"].append(line.strip())
    return blocks


def switch_lines(text: str) -> list[str]:
    return [l.strip() for l in text.splitlines() if l.strip().startswith("switchInt(")]


def normal_path_events(text: str, switch_choice: str | None, stop_call: str) -> dict:
    """Follow the non-unwinding path of a MIR body from `bb0`.

    At a `switchInt` the edge labelled `switch_choice` is taken. The walk stops
    at the first call to `stop_call`. Returns the ordered `drop(..)` /
    `StorageDead(..)` / `push(..)` events and the destructor log they imply
    (a `Guard(const K_u64)` local dropped contributes digit K; `push(const
    K_u64)` contributes digit K), which is what the program prints at runtime.
    """
    blocks = parse_mir_blocks(text)
    guard_of: dict[str, str] = {}
    events: list[str] = []
    log = ""
    bb = "bb0"
    seen = set()
    while bb not in seen:
        seen.add(bb)
        lines = blocks[bb]["lines"]
        for stmt in lines[:-1]:
            m = re.match(r"^(_\d+) = Guard\(const (\d+)_u64\);$", stmt)
            if m:
                guard_of[m.group(1)] = m.group(2)
            elif stmt.startswith("StorageDead("):
                events.append(stmt.rstrip(";"))
        term = lines[-1]
        m = re.match(r"^drop\((_\d+)\) -> \[return: (bb\d+),", term)
        if m:
            events.append(f"drop({m.group(1)})")
            log += guard_of.get(m.group(1), "?")
            bb = m.group(2)
            continue
        m = re.match(r"^_\d+ = (\S+?)\((.*?)\) -> \[return: (bb\d+),", term)
        if m:
            callee, args, nxt = m.group(1), m.group(2), m.group(3)
            if callee == stop_call:
                break
            if callee == "push":
                digit = re.match(r"^const (\d+)_u64$", args).group(1)
                events.append(f"push({digit})")
                log += digit
            bb = nxt
            continue
        m = re.match(r"^switchInt\(.*\) -> \[(.*)\];$", term)
        if m:
            targets = dict(part.strip().split(": ") for part in m.group(1).split(","))
            if switch_choice not in targets:
                raise RuntimeError(f"switch label {switch_choice!r} missing in {term!r}")
            bb = targets[switch_choice]
            continue
        m = re.match(r"^goto -> (bb\d+);$", term)
        if m:
            bb = m.group(1)
            continue
        if term == "return;":
            break
        raise RuntimeError(f"unhandled terminator {term!r}")
    guards = {local: f"Guard({k})" for local, k in sorted(guard_of.items())}
    return {"guard_locals": guards, "events": events, "implied_log": log}


def dump_mir(runner: Runner, source: str, pass_name: str, extra: list[str], tag: str) -> dict:
    """Run rustc with `-Zdump-mir=<pass>` and return {fn: {before, after}}."""
    out_dir = runner.workdir / f"mir_{tag}"
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir()
    result = runner.rustc_run(
        [
            *extra,
            f"-Zdump-mir={pass_name}",
            f"-Zdump-mir-dir={out_dir.name}",
            "--emit=mir",
            "-o",
            f"{out_dir.name}/all.mir",
            source,
        ]
    )
    crate = Path(source).stem
    dumps: dict[str, dict] = {}
    for path in sorted(out_dir.glob(f"{crate}.*.{pass_name}.*.mir")):
        parts = path.name.split(".")
        fn_name, when = parts[1], parts[-2]
        dumps.setdefault(fn_name, {})[when] = path.read_text()
    final_mir = (out_dir / "all.mir").read_text() if (out_dir / "all.mir").exists() else ""
    return {"command": compact(result), "dumps": dumps, "final_mir": final_mir}


def function_from_final_mir(final_mir: str, name: str) -> str:
    m = re.search(rf"^fn {re.escape(name)}\(.*?^}}$", final_mir, re.S | re.M)
    return m.group(0) if m else ""


def llvm_function(ir: str, mangled_fragment: str) -> str:
    m = re.search(rf"^define [^\n]*{re.escape(mangled_fragment)}[^\n]*\{{\n.*?^}}$", ir, re.S | re.M)
    return m.group(0) if m else ""


def llvm_switch_default_is_unreachable(fn_ir: str) -> bool | None:
    """True iff the first `switch`'s default label is a block that only holds
    `unreachable`. None if the function has no `switch`."""
    m = re.search(r"switch i\d+ %\S+, label %(\S+) \[", fn_ir)
    if not m:
        return None
    label = m.group(1)
    body = re.search(rf"^{re.escape(label)}:[^\n]*\n((?:  [^\n]*\n)+)", fn_ir, re.M)
    if not body:
        return False
    insts = [l.strip() for l in body.group(1).splitlines() if l.strip()]
    return insts == ["unreachable"]


def norm_lines(text: str) -> list[str]:
    return [l.rstrip() for l in text.strip().splitlines()]


# --------------------------------------------------------------------------
# Probe sections
# --------------------------------------------------------------------------

DROP_ORDER_FUNCTIONS = {
    # function -> (switch edge to follow, or None when the body has no switch)
    "run_tail_expr": None,
    "fn_body_tail": None,
    "run_if_let_else": "otherwise",
    "run_if_let_then": "1",
    "run_match": "otherwise",
    "run_match_block_scrutinee": "otherwise",
}


def probe_drop_order(r: Runner) -> dict:
    section: dict[str, dict] = {}
    for ed in EDITIONS:
        build = r.rustc_run(["--edition", ed, "-o", f"drop_order_{ed}", "drop_order.rs"])
        native = r.exe_run(f"drop_order_{ed}") if build["rc"] == 0 else None
        miri = r.miri_run(["--edition", ed, "drop_order.rs"])
        mir = dump_mir(r, "drop_order.rs", "ElaborateDrops", ["--edition", ed], f"drops_{ed}")
        functions = {}
        for fn_name, choice in DROP_ORDER_FUNCTIONS.items():
            after = mir["dumps"][fn_name]["after"]
            stop = "take_log" if fn_name != "fn_body_tail" else "<none>"
            functions[fn_name] = {
                "mir_after_elaborate_drops": after,
                "normal_path": normal_path_events(after, choice, stop),
            }
        section[f"edition_{ed}"] = {
            "native_build": compact(build),
            "native_run": compact(native) if native else None,
            "miri_run": compact(miri),
            "mir_dump_command": mir["command"],
            "functions": functions,
        }
    return section


def kv(stdout: str) -> dict:
    return dict(tok.split("=", 1) for tok in stdout.split() if "=" in tok)


def probe_compile_time(r: Runner) -> dict:
    section: dict[str, dict] = {}
    for source in ("tail_temp_borrows_local.rs", "block_tail_temp_escapes.rs"):
        stem = Path(source).stem
        per_edition = {}
        for ed in EDITIONS:
            build = r.rustc_run(["--edition", ed, "-o", f"{stem}_{ed}", source])
            entry = {"build": compact(build)}
            if build["rc"] == 0:
                entry["native_run"] = compact(r.exe_run(f"{stem}_{ed}"))
                entry["miri_run"] = compact(r.miri_run(["--edition", ed, source]))
            per_edition[f"edition_{ed}"] = entry
        section[stem] = per_edition
    svp = {}
    for ed in EDITIONS:
        place = r.rustc_run(["--edition", ed, "-o", f"svp_place_{ed}", "scrutinee_value_vs_place.rs"])
        value = r.rustc_run(
            ["--edition", ed, "--cfg", "value_scrutinee", "-o", f"svp_value_{ed}", "scrutinee_value_vs_place.rs"]
        )
        entry = {"place_scrutinee_build": compact(place), "value_scrutinee_build": compact(value)}
        if place["rc"] == 0:
            entry["place_scrutinee_run"] = compact(r.exe_run(f"svp_place_{ed}"))
        entry["value_scrutinee_e0507_span_lines"] = [
            l for l in value["stderr"].splitlines() if "match unsafe { *p }" in l or "move occurs" in l
        ][:3]
        svp[f"edition_{ed}"] = entry
    section["scrutinee_value_vs_place"] = svp
    return section


def probe_mutex(r: Runner) -> dict:
    section = {}
    for ed in EDITIONS:
        build = r.rustc_run(["--edition", ed, "-o", f"mutex_{ed}", "if_let_mutex_guard.rs"])
        section[f"edition_{ed}"] = {
            "native_build": compact(build),
            "native_run": compact(r.exe_run(f"mutex_{ed}")) if build["rc"] == 0 else None,
            "miri_run": compact(r.miri_run(["--edition", ed, "if_let_mutex_guard.rs"])),
        }
    return section


ENUM_FUNCTIONS = ("classify_raw_wildcard", "classify_raw_value", "classify_ref")
BUILD_CONFIGS = {
    "opt0_miropt0": ["-C", "opt-level=0", "-Zmir-opt-level=0"],
    "opt0_default": ["-C", "opt-level=0"],
    "opt3_miropt0": ["-C", "opt-level=3", "-Zmir-opt-level=0"],
    "opt3_default": ["-C", "opt-level=3"],
}
FORGED_TAG_CFGS = ("tag1_place", "tag1_value", "tag3_place")


def probe_enum_branching(r: Runner) -> dict:
    ed = ["--edition", "2024"]
    section: dict[str, object] = {}

    dump = dump_mir(r, "enum_branching.rs", "UnreachableEnumBranching", [*ed, "-C", "opt-level=3"], "ueb")
    passes = {}
    for fn_name in ENUM_FUNCTIONS:
        before = dump["dumps"][fn_name]["before"]
        after = dump["dumps"][fn_name]["after"]
        passes[fn_name] = {
            "mir_before": before,
            "mir_after": after,
            "switch_before": switch_lines(before),
            "switch_after": switch_lines(after),
            "discriminant_statements_before": [
                l.strip() for l in before.splitlines() if "discriminant(" in l or "= copy (*_1);" in l
            ],
            "unreachable_blocks_before": sum(1 for b in parse_mir_blocks(before).values() if b["lines"][-1] == "unreachable;"),
            "unreachable_blocks_after": sum(1 for b in parse_mir_blocks(after).values() if b["lines"][-1] == "unreachable;"),
        }
    section["pass_dump_command"] = dump["command"]
    section["pass_before_after"] = passes

    configs = {}
    for name, flags in BUILD_CONFIGS.items():
        emitted = dump_mir(r, "enum_branching.rs", "UnreachableEnumBranching", [*ed, *flags], f"cfg_{name}")
        fn_mir = function_from_final_mir(emitted["final_mir"], "classify_raw_wildcard")
        configs[name] = {
            "flags": flags,
            "pass_dump_files_written": sorted(emitted["dumps"].keys()) != [],
            "final_switch": switch_lines(fn_mir),
            "final_mir_has_unreachable_block": any(
                b["lines"][-1] == "unreachable;" for b in parse_mir_blocks(fn_mir).values()
            ),
        }
    section["final_mir_by_build_config"] = configs

    # LLVM IR as emitted by rustc's codegen, before any LLVM optimization
    # (`-C no-prepopulate-passes`), so the function is neither merged with an
    # identical one nor simplified.
    llvm = {}
    for name in ("opt3_default", "opt3_miropt0"):
        out = f"enum_branching_{name}.ll"
        res = r.rustc_run(
            [*ed, *BUILD_CONFIGS[name], "-C", "no-prepopulate-passes", "--emit=llvm-ir", "-o", out, "enum_branching.rs"]
        )
        ir = (r.workdir / out).read_text() if res["rc"] == 0 else ""
        fn_ir = llvm_function(ir, "classify_raw_wildcard")
        range_node = None
        m = re.search(r"load i8, ptr %p[^\n]*!range (!\d+)", fn_ir)
        if m:
            node = re.search(rf"^{re.escape(m.group(1))} = (.*)$", ir, re.M)
            range_node = node.group(1) if node else None
        llvm[name] = {
            "command": compact(res),
            "function_ir": r.scrub(fn_ir),
            "switch_default_is_unreachable": llvm_switch_default_is_unreachable(fn_ir),
            "tag_load_range_metadata": range_node,
        }
    section["llvm_ir_classify_raw_wildcard"] = llvm

    miri = {}
    for level in ("0", "2"):
        valid = r.miri_run([*ed, f"-Zmir-opt-level={level}", "enum_branching.rs"])
        entry = {
            "valid_tags": compact(valid),
            # Miri prints this warning when MIR optimizations are switched on,
            # because it runs without them by default.
            "warns_mir_optimizations_explicitly_enabled": "explicitly enabled MIR optimizations" in valid["stderr"],
        }
        for cfg in FORGED_TAG_CFGS:
            res = r.miri_run([*ed, f"-Zmir-opt-level={level}", "--cfg", cfg, "enum_branching.rs"])
            ub_lines = [l for l in res["stderr"].splitlines() if l.startswith("error: Undefined Behavior")]
            spans = [l for l in res["stderr"].splitlines() if "Undefined Behavior occurred here" in l]
            entry[cfg] = {**compact(res), "ub_lines": ub_lines, "ub_span_lines": spans[:1]}
        miri[f"mir_opt_level_{level}"] = entry
    section["miri"] = miri

    native = {}
    for name, flags in BUILD_CONFIGS.items():
        per_cfg = {}
        for cfg in (None, *FORGED_TAG_CFGS):
            exe = f"eb_{name}_{cfg or 'valid'}"
            cfg_flags = ["--cfg", cfg] if cfg else []
            build = r.rustc_run([*ed, *flags, *cfg_flags, "-o", exe, "enum_branching.rs"])
            run = r.exe_run(exe) if build["rc"] == 0 else None
            per_cfg[cfg or "valid_tags"] = {
                "build_rc": build["rc"],
                "run": compact(run) if run else None,
                "executes_undefined_behavior": cfg is not None,
            }
        native[name] = per_cfg
    section["native_runs"] = native
    return section


def compare_with_retained(results: dict, retained: dict) -> dict:
    """Compare this run with a receipt retained from another toolchain."""
    comparisons = {}
    part_a = retained["edition_drop_orders"]
    for ed in EDITIONS:
        mine = results["drop_order"][f"edition_{ed}"]
        theirs = part_a[f"edition_{ed}"]
        first_line = (mine["native_run"]["stdout"].splitlines() or [""])[0]
        comparisons[f"edition_{ed}_native_first_line"] = {
            "this_run": first_line,
            "retained": theirs["native_stdout"],
            "identical": first_line == theirs["native_stdout"],
        }
        miri_first = (mine["miri_run"]["stdout"].splitlines() or [""])[0]
        comparisons[f"edition_{ed}_miri_first_line"] = {
            "this_run": miri_first,
            "retained": theirs["miri_stdout"],
            "identical": miri_first == theirs["miri_stdout"],
        }
        for fn_name, key in (("run_tail_expr", "tail_elaborated_mir"), ("run_if_let_else", "if_let_elaborated_mir")):
            a = norm_lines(mine["functions"][fn_name]["mir_after_elaborate_drops"])
            b = norm_lines(theirs[key])
            comparisons[f"edition_{ed}_{fn_name}_mir"] = {
                "identical": a == b,
                "diff": list(difflib.unified_diff(b, a, "retained", "this_run", lineterm=""))[:60],
            }
    part_b = retained["unreachable_enum_branching"]
    mine_b = results["enum_branching"]["pass_before_after"]["classify_raw_wildcard"]
    for when, key in (("before", "classify_raw_wildcard_before_mir"), ("after", "classify_raw_wildcard_after_mir")):
        a = norm_lines(mine_b[f"mir_{when}"])
        b = norm_lines(part_b[key])
        comparisons[f"classify_raw_wildcard_{when}_mir"] = {
            "identical": a == b,
            "diff": list(difflib.unified_diff(b, a, "retained", "this_run", lineterm=""))[:60],
        }
    return {"retained_rustc_version": retained["rustc_version"], "comparisons": comparisons}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rustc", default=shutil.which("rustc") or "rustc")
    ap.add_argument("--miri", default=shutil.which("miri") or "miri")
    ap.add_argument("--miri-sysroot", default=os.environ.get("MIRI_SYSROOT", ""))
    ap.add_argument("--retained-receipt", default=None)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    with tempfile.TemporaryDirectory(prefix="ed2024_probe_") as tmp:
        workdir = Path(tmp)
        for name in SOURCES:
            shutil.copy(RUST_DIR / name, workdir / name)
        r = Runner(args.rustc, args.miri, args.miri_sysroot, workdir)
        results: dict[str, object] = {
            "schema": "edition-drop-scopes-and-enum-branching-probe/1",
            "toolchain": {
                "rustc_verbose_version": r.rustc_run(["-Vv"])["stdout"].strip(),
                "miri_version": r.run([args.miri, "--version"])["stdout"].strip(),
            },
            "sources": sorted(SOURCES),
        }
        results["drop_order"] = probe_drop_order(r)
        results["compile_time"] = probe_compile_time(r)
        results["mutex_guard"] = probe_mutex(r)
        results["enum_branching"] = probe_enum_branching(r)

    if args.retained_receipt:
        retained = json.loads(Path(args.retained_receipt).read_text())
        results["retained_receipt_comparison"] = compare_with_retained(results, retained)

    # ---------------------------------------------------------------- checks
    checks: list[dict] = []

    def check(name: str, observed, expected) -> None:
        checks.append({"name": name, "observed": observed, "expected": expected, "ok": observed == expected})

    d = results["drop_order"]
    expected_logs = {
        "2021": {"TAIL": "12", "IF_LET": "91", "MATCH": "91", "FN_TAIL": "12", "IF_LET_THEN": "81", "MATCH_BLOCK_SCRUTINEE": "91"},
        "2024": {"TAIL": "21", "IF_LET": "19", "MATCH": "91", "FN_TAIL": "21", "IF_LET_THEN": "81", "MATCH_BLOCK_SCRUTINEE": "19"},
    }
    mir_fn_for = {
        "TAIL": "run_tail_expr",
        "FN_TAIL": "fn_body_tail",
        "IF_LET": "run_if_let_else",
        "IF_LET_THEN": "run_if_let_then",
        "MATCH": "run_match",
        "MATCH_BLOCK_SCRUTINEE": "run_match_block_scrutinee",
    }
    for ed in EDITIONS:
        e = d[f"edition_{ed}"]
        check(f"drop_order/{ed}/native", kv(e["native_run"]["stdout"]), expected_logs[ed])
        check(f"drop_order/{ed}/miri", kv(e["miri_run"]["stdout"]), expected_logs[ed])
        check(f"drop_order/{ed}/miri_rc", e["miri_run"]["rc"], 0)
        for key, fn_name in mir_fn_for.items():
            check(
                f"drop_order/{ed}/mir_implied_log/{fn_name}",
                e["functions"][fn_name]["normal_path"]["implied_log"],
                expected_logs[ed][key],
            )

    c = results["compile_time"]
    t = c["tail_temp_borrows_local"]
    check("tail_temp_borrows_local/2021/error_codes", t["edition_2021"]["build"]["error_codes"], ["E0597"])
    check("tail_temp_borrows_local/2024/build_rc", t["edition_2024"]["build"]["rc"], 0)
    check("tail_temp_borrows_local/2024/native", t["edition_2024"].get("native_run", {}).get("stdout", "").strip(), "LEN=3")
    check("tail_temp_borrows_local/2024/miri", t["edition_2024"].get("miri_run", {}).get("stdout", "").strip(), "LEN=3")
    b = c["block_tail_temp_escapes"]
    check("block_tail_temp_escapes/2021/native", b["edition_2021"].get("native_run", {}).get("stdout", "").strip(), "N=4")
    check("block_tail_temp_escapes/2021/miri", b["edition_2021"].get("miri_run", {}).get("stdout", "").strip(), "N=4")
    check("block_tail_temp_escapes/2024/error_codes", b["edition_2024"]["build"]["error_codes"], ["E0716"])
    for ed in EDITIONS:
        s = c["scrutinee_value_vs_place"][f"edition_{ed}"]
        check(f"scrutinee_value_vs_place/{ed}/place_build_rc", s["place_scrutinee_build"]["rc"], 0)
        check(f"scrutinee_value_vs_place/{ed}/place_run", s.get("place_scrutinee_run", {}).get("stdout", "").strip(), "PLACE=41")
        check(f"scrutinee_value_vs_place/{ed}/value_error_codes", s["value_scrutinee_build"]["error_codes"], ["E0507"])

    m = results["mutex_guard"]
    expected_mutex = {
        "2021": {"IF_LET_ELSE_LOCK": "held", "MATCH_ARM_LOCK": "held"},
        "2024": {"IF_LET_ELSE_LOCK": "released", "MATCH_ARM_LOCK": "held"},
    }
    for ed in EDITIONS:
        check(f"mutex_guard/{ed}/native", kv(m[f"edition_{ed}"]["native_run"]["stdout"]), expected_mutex[ed])
        check(f"mutex_guard/{ed}/miri", kv(m[f"edition_{ed}"]["miri_run"]["stdout"]), expected_mutex[ed])

    eb = results["enum_branching"]
    pb = eb["pass_before_after"]
    check("ueb/classify_raw_wildcard/switch_before", pb["classify_raw_wildcard"]["switch_before"], ["switchInt(move _2) -> [0: bb2, otherwise: bb1];"])
    check("ueb/classify_raw_wildcard/switch_after", pb["classify_raw_wildcard"]["switch_after"], ["switchInt(move _2) -> [0: bb2, 2: bb1, otherwise: bb4];"])
    check("ueb/classify_raw_wildcard/unreachable_blocks", [pb["classify_raw_wildcard"]["unreachable_blocks_before"], pb["classify_raw_wildcard"]["unreachable_blocks_after"]], [0, 1])
    check("ueb/classify_raw_wildcard/place_discriminant", pb["classify_raw_wildcard"]["discriminant_statements_before"], ["_2 = discriminant((*_1));"])
    check("ueb/classify_raw_value/copy_then_discriminant", pb["classify_raw_value"]["discriminant_statements_before"], ["_2 = copy (*_1);", "_3 = discriminant(_2);"])
    check("ueb/classify_raw_value/switch_after", pb["classify_raw_value"]["switch_after"], ["switchInt(move _3) -> [0: bb2, 2: bb1, otherwise: bb4];"])
    check("ueb/classify_ref/switch_before", pb["classify_ref"]["switch_before"], ["switchInt(move _2) -> [0: bb4, 1: bb3, 2: bb2, otherwise: bb1];"])
    check("ueb/classify_ref/switch_after", pb["classify_ref"]["switch_after"], ["switchInt(move _2) -> [0: bb4, 1: bb1, 2: bb2, otherwise: bb1];"])
    cfgs = eb["final_mir_by_build_config"]
    check(
        "ueb/final_mir_has_unreachable_block_by_config",
        {k: v["final_mir_has_unreachable_block"] for k, v in cfgs.items()},
        {"opt0_miropt0": False, "opt0_default": True, "opt3_miropt0": False, "opt3_default": True},
    )
    ll = eb["llvm_ir_classify_raw_wildcard"]
    check(
        "ueb/llvm_switch_default_is_unreachable",
        {k: v["switch_default_is_unreachable"] for k, v in ll.items()},
        {"opt3_default": True, "opt3_miropt0": None},
    )
    check(
        "ueb/llvm_tag_load_range_metadata",
        {k: v["tag_load_range_metadata"] for k, v in ll.items()},
        {"opt3_default": "!{i8 0, i8 3}", "opt3_miropt0": "!{i8 0, i8 3}"},
    )
    expected_ub = {
        "tag1_place": ["error: Undefined Behavior: read discriminant of an uninhabited enum variant"],
        "tag1_value": ["error: Undefined Behavior: constructing invalid value of type Tri: at .<enum-tag>, encountered an uninhabited enum variant"],
        "tag3_place": ["error: Undefined Behavior: enum value has invalid tag: 0x03"],
    }
    for level in ("0", "2"):
        mi = eb["miri"][f"mir_opt_level_{level}"]
        check(f"ueb/miri/{level}/valid_rc", mi["valid_tags"]["rc"], 0)
        check(f"ueb/miri/{level}/valid_stdout", mi["valid_tags"]["stdout"].strip(), "VALID A=42 C=77 A_VALUE=42 C_VALUE=77 A_REF=42 C_REF=77")
        check(f"ueb/miri/{level}/warns_mir_optimizations_explicitly_enabled", mi["warns_mir_optimizations_explicitly_enabled"], level != "0")
        for cfg, lines in expected_ub.items():
            check(f"ueb/miri/{level}/{cfg}/rc", mi[cfg]["rc"], 1)
            check(f"ueb/miri/{level}/{cfg}/ub_lines", mi[cfg]["ub_lines"], lines)
    for name in BUILD_CONFIGS:
        check(
            f"ueb/native/{name}/valid_stdout",
            eb["native_runs"][name]["valid_tags"]["run"]["stdout"].strip(),
            "VALID A=42 C=77 A_VALUE=42 C_VALUE=77 A_REF=42 C_REF=77",
        )

    if "retained_receipt_comparison" in results:
        for name, cmp in results["retained_receipt_comparison"]["comparisons"].items():
            check(f"retained/{name}/identical", cmp["identical"], True)

    results["checks"] = checks
    results["checks_total"] = len(checks)
    results["checks_failed"] = [c["name"] for c in checks if not c["ok"]]

    blob = json.dumps(results, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    # Any absolute filesystem path (a slash-led path with two or more segments
    # that starts a token) would be a scrubbing failure.
    leaks = sorted(set(re.findall(r"(?:(?<=[\s\"'=:(\[])|^)/[A-Za-z0-9_.+-]+(?:/[A-Za-z0-9_.+-]+)+", blob)))
    if leaks:
        print("refusing to write output containing absolute paths:", leaks[:5], file=sys.stderr)
        return 2
    Path(args.out).write_text(blob)
    print(f"{len(checks) - len(results['checks_failed'])}/{len(checks)} checks passed")
    for name in results["checks_failed"]:
        print("FAILED:", name, file=sys.stderr)
    return 1 if results["checks_failed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
