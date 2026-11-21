#!/usr/bin/env python3
"""Probe `rustc`'s `ElaborateDrops` pass on real MIR and at run time.

What this script does (nothing in its output is typed in by hand):

1. compiles the Rust files in `support/specimens/` with the `rustc` found on
   `PATH` (or `--rustc`), once with `-C panic=unwind` and once with
   `-C panic=abort`, asking the compiler to dump the MIR of every specimen
   function immediately before and after the `ElaborateDrops` pass, around
   `AbortUnwindingCalls`, and at `runtime-post-cleanup`;
2. parses those dumps and counts locals, `bool` locals added by the pass (drop
   flags), basic blocks, cleanup blocks, `drop` terminators, flag tests, flag
   writes and unwind edges by kind, and classifies every pre-elaboration `drop`
   terminator by the shape of what replaced it;
3. runs every specimen natively with argument `0` and `1`, recording standard
   output (one line per destructor run), the exit status or signal and the
   panic-runtime messages on standard error;
4. evaluates a list of checks over the measured data and writes
   `probe_results.json`, `probe_summary.md` and the raw MIR dumps.

Usage:

    python3 support/probe_drop_elaboration.py --out support/probe_output

The script needs a nightly `rustc` (it uses `-Z` flags and `#[custom_mir]`).
It exits non-zero if a check fails.

Classification of a pre-elaboration `drop(P) -> [return: T, ...]` in block `B`
(a syntactic reading of the post-elaboration dump, not compiler output):

* `static`       block `B` still ends in `drop(P)`;
* `dead`         block `B` now ends in `goto -> T`;
* `conditional`  block `B` jumps to blocks created by the pass which test a
                 flag local and drop exactly `P`;
* `open`         block `B` jumps to blocks created by the pass which drop
                 projections of `P` (fields, downcasts, elements);
* `other`        anything else (reported, never silently merged).
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPECIMEN_DIR = HERE / "specimens"

MAIN_FILE = "drop_specimens.rs"
CUSTOM_FILE = "custom_mir_specimens.rs"
INVALID_FILE = "custom_mir_cleanup_continue.rs"

DUMP_FILTER = "ElaborateDrops | AbortUnwindingCalls | runtime-post-cleanup"

# Functions analysed although `main` does not dispatch to them directly.
EXTRA_ANALYSED = {"generic_cond_move"}

LOCAL_RE = re.compile(r"^\s+let (?:mut )?(_\d+): (.+);$")
BLOCK_RE = re.compile(r"^\s+(bb\d+)( \(cleanup\))?: \{$")
FN_RE = re.compile(r"^(?:extern \"[^\"]*\" )?fn ([^(]+)\((.*)\) -> (.+) \{$")
DROP_RE = re.compile(r"^drop\((.+)\) -> \[return: (bb\d+), unwind(.*)\];$")
GOTO_RE = re.compile(r"^goto -> (bb\d+);$")
SWITCH_COPY_RE = re.compile(r"^switchInt\(copy (_\d+)\) -> \[(.*)\];$")
ASSIGN_CONST_BOOL_RE = re.compile(r"^(_\d+) = const (true|false);$")
BB_REF_RE = re.compile(r"bb\d+")


def run(cmd, cwd=None, env=None, timeout=600):
    proc = subprocess.run(
        cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout
    )
    return proc.returncode, proc.stdout.decode("utf-8", "replace"), proc.stderr.decode("utf-8", "replace")


def sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# --------------------------------------------------------------------------- MIR parsing


def parse_mir(text: str) -> dict:
    """Parse one `-Zdump-mir` file into locals and blocks."""
    lines = text.splitlines()
    fn_name = None
    args = []
    locals_ = {}
    blocks = []
    cur = None
    for line in lines:
        if fn_name is None:
            m = FN_RE.match(line)
            if m:
                fn_name = m.group(1)
                for a in m.group(2).split(", "):
                    am = re.match(r"^(_\d+): (.+)$", a.strip())
                    if am:
                        args.append((am.group(1), am.group(2)))
            continue
        if cur is None:
            lm = LOCAL_RE.match(line)
            if lm:
                locals_[lm.group(1)] = lm.group(2)
                continue
            bm = BLOCK_RE.match(line)
            if bm:
                cur = {"name": bm.group(1), "cleanup": bm.group(2) is not None, "lines": []}
                continue
        else:
            if re.match(r"^\s+\}$", line):
                stmts = [s.strip() for s in cur["lines"] if s.strip()]
                cur["terminator"] = stmts[-1] if stmts else ""
                cur["statements"] = stmts[:-1]
                del cur["lines"]
                blocks.append(cur)
                cur = None
            else:
                cur["lines"].append(line)
    if fn_name is None:
        raise ValueError("no MIR function header found")
    return {"function": fn_name, "args": args, "locals": locals_, "blocks": blocks}


def unwind_kind(term: str) -> str | None:
    if "unwind terminate(cleanup)" in term:
        return "terminate_cleanup"
    if "unwind terminate(abi)" in term:
        return "terminate_abi"
    if "unwind continue" in term:
        return "continue"
    if "unwind unreachable" in term:
        return "unreachable"
    if re.search(r"unwind: bb\d+", term):
        return "cleanup"
    return None


def mir_stats(mir: dict, flag_locals: set[str] | None = None) -> dict:
    flag_locals = flag_locals or set()
    blocks = mir["blocks"]
    unwind = {"cleanup": 0, "continue": 0, "terminate_cleanup": 0, "terminate_abi": 0, "unreachable": 0}
    drops = 0
    drops_in_cleanup = 0
    flag_tests = 0
    flag_writes = {"true": 0, "false": 0}
    resume = 0
    terminate = 0
    for b in blocks:
        t = b["terminator"]
        k = unwind_kind(t)
        if k:
            unwind[k] += 1
        if t.startswith("drop("):
            drops += 1
            if b["cleanup"]:
                drops_in_cleanup += 1
        sm = SWITCH_COPY_RE.match(t)
        if sm and sm.group(1) in flag_locals:
            flag_tests += 1
        if t == "resume;":
            resume += 1
        if t.startswith("terminate("):
            terminate += 1
        for s in b["statements"]:
            am = ASSIGN_CONST_BOOL_RE.match(s)
            if am and am.group(1) in flag_locals:
                flag_writes[am.group(2)] += 1
    return {
        "locals": len(mir["locals"]) + len(mir["args"]),
        "bool_locals": sum(1 for ty in mir["locals"].values() if ty == "bool"),
        "blocks": len(blocks),
        "cleanup_blocks": sum(1 for b in blocks if b["cleanup"]),
        "drop_terminators": drops,
        "drop_terminators_in_cleanup": drops_in_cleanup,
        "resume_terminators": resume,
        "terminate_terminators": terminate,
        "unwind_edges": unwind,
        "flag_tests": flag_tests,
        "flag_writes": flag_writes,
    }


def classify_drops(pre: dict, post: dict, flag_locals: set[str]) -> list[dict]:
    """Classify every pre-elaboration drop by what replaced it (see module docstring)."""
    n_pre = len(pre["blocks"])
    post_by_name = {b["name"]: b for b in post["blocks"]}
    created = {b["name"] for b in post["blocks"] if int(b["name"][2:]) >= n_pre}
    out = []
    for b in pre["blocks"]:
        m = DROP_RE.match(b["terminator"])
        if not m:
            continue
        place, target = m.group(1), m.group(2)
        pre_unwind = unwind_kind(b["terminator"])
        pb = post_by_name.get(b["name"])
        style = "other"
        ladder = {"blocks": 0, "cleanup_blocks": 0, "flag_tests": 0, "drops": []}
        if pb is not None:
            pt = pb["terminator"]
            pm = DROP_RE.match(pt)
            gm = GOTO_RE.match(pt)
            if pm and pm.group(1) == place:
                style = "static"
            elif gm and gm.group(1) == target:
                style = "dead"
            elif gm and gm.group(1) in created:
                seen = set()
                work = [gm.group(1)]
                tests = 0
                dropped = []
                while work:
                    name = work.pop()
                    if name in seen or name not in created:
                        continue
                    seen.add(name)
                    lb = post_by_name[name]
                    lt = lb["terminator"]
                    sm = SWITCH_COPY_RE.match(lt)
                    if sm and sm.group(1) in flag_locals:
                        tests += 1
                    dm = DROP_RE.match(lt)
                    if dm:
                        dropped.append(dm.group(1))
                    for ref in BB_REF_RE.findall(lt):
                        work.append(ref)
                ladder = {
                    "blocks": len(seen),
                    "cleanup_blocks": sum(1 for n in seen if post_by_name[n]["cleanup"]),
                    "flag_tests": tests,
                    "drops": sorted(set(dropped)),
                }
                if any(d != place for d in dropped):
                    style = "open"
                elif tests > 0 and dropped:
                    style = "conditional"
        out.append(
            {
                "block": b["name"],
                "in_cleanup_block": b["cleanup"],
                "place": place,
                "pre_unwind": pre_unwind,
                "style": style,
                "ladder": ladder,
            }
        )
    return out


DROP_FULL_RE = re.compile(r"^drop\((.+)\) -> \[return: (bb\d+), unwind(?:: (bb\d+)| (terminate\(cleanup\)))\];$")
SWITCH_FULL_RE = re.compile(r"^switchInt\(copy (_\d+)\) -> \[0: (bb\d+), otherwise: (bb\d+)\];$")


def open_ladder_shape(post: dict, flag_locals: set[str]) -> list[dict]:
    """Find every instance, among non-cleanup blocks, of the two-field open-drop ladder

        T: switchInt(copy flag) -> [0: B, otherwise: A]
        A: drop(P.0) -> [return: B, unwind: C]
        B: drop(P.1) -> [return: _, unwind: U]        U: resume
        C (cleanup): drop(P.1) -> [return: U, unwind terminate(cleanup)]

    and report the blocks involved. This is the shape that the Lean theorem
    `DropElab.Example.condFieldMove_ladder` states for the model's elaboration."""
    by_name = {b["name"]: b for b in post["blocks"]}
    found = []
    for t in post["blocks"]:
        if t["cleanup"]:
            continue
        sm = SWITCH_FULL_RE.match(t["terminator"])
        if not sm or sm.group(1) not in flag_locals:
            continue
        b_blk, a_blk = by_name.get(sm.group(2)), by_name.get(sm.group(3))
        if a_blk is None or b_blk is None:
            continue
        am = DROP_FULL_RE.match(a_blk["terminator"])
        bm = DROP_FULL_RE.match(b_blk["terminator"])
        if not am or not bm or am.group(2) != b_blk["name"] or am.group(3) is None or bm.group(3) is None:
            continue
        c_blk, u_blk = by_name.get(am.group(3)), by_name.get(bm.group(3))
        if c_blk is None or u_blk is None or not c_blk["cleanup"] or u_blk["terminator"] != "resume;":
            continue
        cm = DROP_FULL_RE.match(c_blk["terminator"])
        if not cm or cm.group(1) != bm.group(1) or cm.group(2) != u_blk["name"] or cm.group(4) is None:
            continue
        found.append(
            {
                "flag": sm.group(1),
                "test_block": t["name"],
                "first_field_drop": {"block": a_blk["name"], "place": am.group(1)},
                "second_field_drop": {"block": b_blk["name"], "place": bm.group(1)},
                "unwind_second_field_drop": {"block": c_blk["name"], "place": cm.group(1), "unwind": "terminate(cleanup)"},
                "resume_block": u_blk["name"],
            }
        )
    return found


def collect_function_dumps(dump_dir: Path, crate: str) -> dict:
    """Group dump files by function: {fn: {dump_name: path}}."""
    out: dict[str, dict[str, Path]] = {}
    for p in sorted(dump_dir.glob(f"{crate}.*.mir")):
        parts = p.name[len(crate) + 1 :].split(".")
        # <fn>.<n-n-nnn>.<pass>.<before|after>.mir
        if len(parts) < 5:
            continue
        fn, _idx, pass_name, when = parts[0], parts[1], parts[2], parts[3]
        out.setdefault(fn, {})[f"{pass_name}.{when}"] = p
    return out


def analyse_function(dump_files: dict[str, Path]) -> dict:
    if "ElaborateDrops.before" not in dump_files or "ElaborateDrops.after" not in dump_files:
        # Runtime-dialect hand-written bodies never go through `ElaborateDrops`.
        result = {"elaborate_drops_dumped": False}
        if "runtime-post-cleanup.after" in dump_files:
            result["runtime_post_cleanup_after"] = mir_stats(
                parse_mir(dump_files["runtime-post-cleanup.after"].read_text())
            )
        return result
    pre = parse_mir(dump_files["ElaborateDrops.before"].read_text())
    post = parse_mir(dump_files["ElaborateDrops.after"].read_text())
    flag_locals = {
        name for name, ty in post["locals"].items() if ty == "bool" and name not in pre["locals"]
    }
    pre_s = mir_stats(pre)
    post_s = mir_stats(post, flag_locals)
    drops = classify_drops(pre, post, flag_locals)
    styles = {}
    for d in drops:
        styles[d["style"]] = styles.get(d["style"], 0) + 1
    result = {
        "elaborate_drops_dumped": True,
        "flag_locals": sorted(flag_locals, key=lambda s: int(s[1:])),
        "pre_elaborate_drops": pre_s,
        "post_elaborate_drops": post_s,
        "delta": {
            "bool_locals": post_s["bool_locals"] - pre_s["bool_locals"],
            "blocks": post_s["blocks"] - pre_s["blocks"],
            "cleanup_blocks": post_s["cleanup_blocks"] - pre_s["cleanup_blocks"],
            "drop_terminators": post_s["drop_terminators"] - pre_s["drop_terminators"],
        },
        "pre_drops": drops,
        "style_counts": styles,
        "two_field_open_ladders": open_ladder_shape(post, flag_locals),
    }
    for key in ("AbortUnwindingCalls.before", "AbortUnwindingCalls.after", "runtime-post-cleanup.after"):
        if key in dump_files:
            result[key.replace(".", "_").replace("-", "_")] = mir_stats(
                parse_mir(dump_files[key].read_text()), flag_locals
            )
    return result


# --------------------------------------------------------------------------- native runs

STDERR_MARKERS = (
    "panic in a destructor during cleanup",
    "panic in a function that cannot unwind",
    "thread caused non-unwinding panic. aborting.",
    "thread panicked while processing panic. aborting.",
)


def run_specimen(binary: Path, name: str | None, arg: int | None) -> dict:
    cmd = [str(binary)]
    if name is not None:
        cmd += [name, str(arg)]
    env = dict(os.environ, RUST_BACKTRACE="0")
    rc, out, err = run(cmd, env=env, timeout=60)
    lines = out.splitlines()
    drop_counts: dict[str, int] = {}
    for line in lines:
        if line.startswith("drop "):
            drop_counts[line[5:]] = drop_counts.get(line[5:], 0) + 1
    panic_messages = []
    err_lines = err.splitlines()
    for i, line in enumerate(err_lines):
        if "panicked at" in line and i + 1 < len(err_lines):
            panic_messages.append(err_lines[i + 1].strip())
    return {
        "argument": arg,
        "stdout": lines,
        "exit_code": rc if rc >= 0 else None,
        "signal": signal.Signals(-rc).name if rc < 0 else None,
        "panic_count": sum(1 for line in err_lines if "panicked at" in line),
        "panic_messages": panic_messages,
        "runtime_markers": [m for m in STDERR_MARKERS if m in err],
        "drop_counts": drop_counts,
        "reached_main_return": "main-returned" in lines,
    }


def specimen_names(path: Path) -> list[str]:
    """Names dispatched by `main` (the string literals of its `match`)."""
    text = path.read_text()
    body = text[text.index("fn main()") :]
    return re.findall(r'^\s+"([a-z0-9_]+)" => ', body, flags=re.M)


# --------------------------------------------------------------------------- compile


def compile_file(rustc: str, src: Path, work: Path, panic: str, extra: list[str]) -> dict:
    dump_dir = work / f"mir_{src.stem}_{panic}"
    binary = work / f"{src.stem}_{panic}.bin"
    cmd = [
        rustc,
        "--edition",
        "2021",
        "-C",
        f"panic={panic}",
        "-C",
        "opt-level=0",
        "-C",
        "debuginfo=0",
        f"-Zdump-mir={DUMP_FILTER}",
        f"-Zdump-mir-dir={dump_dir}",
        *extra,
        str(src),
        "-o",
        str(binary),
    ]
    env = dict(os.environ, RUSTC_ICE="0", RUST_BACKTRACE="0")
    rc, out, err = run(cmd, cwd=work, env=env)
    shown = [c.replace(str(work), "$WORK").replace(str(src.parent), "support/specimens") for c in cmd]
    shown[0] = "rustc"
    return {
        "command": shown,
        "exit_code": rc,
        "stderr_excerpt": [line for line in err.splitlines() if line.strip()][:6],
        "binary": binary if rc == 0 and binary.exists() else None,
        "dump_dir": dump_dir,
    }


# --------------------------------------------------------------------------- checks


def find_run(runs, arg):
    for r in runs:
        if r["argument"] == arg:
            return r
    raise KeyError(arg)


def evaluate_checks(results: dict) -> list[dict]:
    checks = []

    def add(name, ok, detail):
        checks.append({"check": name, "pass": bool(ok), "detail": detail})

    unwind = results["configurations"]["panic_unwind"]["functions"]
    abort = results["configurations"]["panic_abort"]["functions"]
    custom = results["configurations"]["custom_mir_unwind"]["functions"]

    # 1. No specimen built by MIR building ever runs a destructor twice.
    worst = 0
    for cfg in (unwind, abort):
        for fn, data in cfg.items():
            for r in data.get("runs", []):
                for n, k in r["drop_counts"].items():
                    worst = max(worst, k)
    add("mir_built_specimens_never_drop_twice", worst <= 1, f"max destructor runs per value = {worst}")

    # 2. Flag synthesis: join-point specimens get flags, straight-line ones do not.
    for fn, expected in (
        ("static_drop", 0),
        ("dead_drop", 0),
        ("early_return", 0),
        ("partial_move_tuple", 0),
        ("manually_drop", 0),
        ("maybe_uninit", 0),
        ("copy_type", 0),
    ):
        n = len(unwind[fn]["flag_locals"])
        add(f"no_flag::{fn}", n == expected, f"flag locals = {n}")
    for fn in ("cond_move", "cond_init", "loop_break_move", "cond_partial_move_tuple", "cond_partial_move_struct"):
        n = len(unwind[fn]["flag_locals"])
        add(f"has_flag::{fn}", n >= 1, f"flag locals = {n}")

    # 3. needs_drop = false: no drop terminator before or after the pass.
    for fn in ("manually_drop", "maybe_uninit", "copy_type"):
        pre = unwind[fn]["pre_elaborate_drops"]["drop_terminators"]
        post = unwind[fn]["post_elaborate_drops"]["drop_terminators"]
        runs = unwind[fn]["runs"]
        ran = sum(sum(r["drop_counts"].values()) for r in runs)
        add(f"no_drop_glue::{fn}", post == 0 and ran == 0, f"pre drops = {pre}, post drops = {post}, destructor runs = {ran}")

    # 4. Conditional move: exactly one destructor run on both branches.
    for fn, value in (("cond_move", "x"), ("loop_break_move", "x"), ("cond_partial_move_tuple", "p0")):
        ok = all(find_run(unwind[fn]["runs"], a)["drop_counts"].get(value, 0) == 1 for a in (0, 1))
        add(f"exactly_once::{fn}", ok, str({a: find_run(unwind[fn]["runs"], a)["drop_counts"] for a in (0, 1)}))

    # 5. Partial move: unmoved siblings are dropped individually.
    r = find_run(unwind["cond_partial_move_struct"]["runs"], 1)
    add(
        "open_drop_siblings::cond_partial_move_struct",
        r["stdout"][-3:] == ["drop s.a", "drop s.c", "main-returned"],
        str(r["stdout"]),
    )

    # 5b. The open-drop ladder of the tuple specimen has the shape stated by the Lean model.
    lad = unwind["cond_partial_move_tuple"]["two_field_open_ladders"]
    add(
        "open_drop_ladder_shape::cond_partial_move_tuple",
        len(lad) == 1
        and lad[0]["first_field_drop"]["place"].endswith(".0: Loud)")
        and lad[0]["second_field_drop"]["place"].endswith(".1: Loud)"),
        json.dumps(lad),
    )

    # 6. Assignment over an initialized place.
    r0 = find_run(unwind["assign_overwrite"]["runs"], 0)
    r1 = find_run(unwind["assign_overwrite"]["runs"], 1)
    add("assign_overwrite::old_dropped_before_new_lives", r0["drop_counts"] == {"old": 1, "new": 1}, str(r0["stdout"]))
    add(
        "assign_overwrite::constructor_panic_drops_old_once",
        r1["drop_counts"] == {"old": 1} and r1["exit_code"] == 101,
        f"stdout = {r1['stdout']}, exit = {r1['exit_code']}",
    )
    r = find_run(unwind["assign_overwrite_old_dtor_panics"]["runs"], 0)
    add(
        "assign_overwrite::assignment_completes_on_unwind_path",
        r["stdout"] == ["drop old", "drop new"] and r["exit_code"] == 101 and r["panic_count"] == 1,
        f"stdout = {r['stdout']}, exit = {r['exit_code']}, panics = {r['panic_count']}",
    )

    # 7. Double panic aborts.
    r = find_run(unwind["double_panic"]["runs"], 0)
    add(
        "double_panic::aborts_with_sigabrt",
        r["signal"] == "SIGABRT" and "panic in a destructor during cleanup" in r["runtime_markers"] and "b" not in r["drop_counts"],
        f"signal = {r['signal']}, markers = {r['runtime_markers']}, stdout = {r['stdout']}",
    )
    r = find_run(unwind["tuple_first_dtor_panics"]["runs"], 0)
    add(
        "glue::one_panic_still_drops_siblings",
        r["stdout"] == ["effect body", "drop t0", "drop t1", "drop t2"] and r["exit_code"] == 101,
        f"stdout = {r['stdout']}, exit = {r['exit_code']}",
    )
    r = find_run(unwind["tuple_two_dtors_panic"]["runs"], 0)
    add(
        "glue::second_panic_aborts_before_third_field",
        r["stdout"] == ["effect body", "drop t0", "drop t1"] and r["signal"] == "SIGABRT",
        f"stdout = {r['stdout']}, signal = {r['signal']}",
    )

    # 8. Destructor runs between the fatal panic and the abort depend on the drop style.
    rs = find_run(unwind["static_glue_in_cleanup"]["runs"], 0)
    ro = find_run(unwind["open_ladder_in_cleanup"]["runs"], 0)
    add(
        "pre_abort_trace_differs_between_static_and_open",
        rs["signal"] == "SIGABRT" and ro["signal"] == "SIGABRT" and rs["stdout"] != ro["stdout"],
        f"static glue stdout = {rs['stdout']}; open ladder stdout = {ro['stdout']}",
    )

    # 9. panic=abort: every unwind edge after AbortUnwindingCalls is `unreachable`, no cleanup blocks.
    bad = []
    for fn, data in abort.items():
        st = data.get("AbortUnwindingCalls_after")
        if st is None:
            continue
        e = st["unwind_edges"]
        if st["cleanup_blocks"] != 0 or e["cleanup"] or e["continue"] or e["terminate_cleanup"] or e["terminate_abi"]:
            bad.append(fn)
    add("panic_abort::no_cleanup_after_abort_unwinding_calls", not bad, f"offending functions = {bad}")

    # 9b. panic=abort does not change what ElaborateDrops does.
    differing = []
    for fn, data in abort.items():
        u = unwind[fn]
        if (
            data["flag_locals"] != u["flag_locals"]
            or data["style_counts"] != u["style_counts"]
            or data["post_elaborate_drops"]["drop_terminators"] != u["post_elaborate_drops"]["drop_terminators"]
            or data["post_elaborate_drops"]["flag_tests"] != u["post_elaborate_drops"]["flag_tests"]
        ):
            differing.append(fn)
    add("panic_abort::same_elaboration_as_unwind", not differing, f"functions whose flags, styles, drops or flag tests differ = {differing}")

    # 9c. panic=abort: the first panic aborts and no destructor runs.
    r = find_run(abort["double_panic"]["runs"], 0)
    add(
        "panic_abort::first_panic_aborts_without_destructors",
        r["signal"] == "SIGABRT" and r["drop_counts"] == {} and r["panic_count"] == 1,
        f"signal = {r['signal']}, stdout = {r['stdout']}, panics = {r['panic_count']}",
    )

    # 9d. Arrays: whole-array glue drops forward, the open ladder drops ranges in reverse.
    rs_ = find_run(unwind["array_static_drop"]["runs"], 0)
    ro_ = find_run(unwind["array_cond_move"]["runs"], 0)
    add(
        "array::open_ladder_reverses_range_order",
        [l for l in rs_["stdout"] if l.startswith("drop ")] == ["drop arr0", "drop arr1"]
        and [l for l in ro_["stdout"] if l.startswith("drop ")] == ["drop arr1", "drop arr0"],
        f"whole-array drop stdout = {rs_['stdout']}; open-ladder stdout = {ro_['stdout']}",
    )

    # 10. extern "C" body: `resume` becomes `terminate(abi)`.
    st_b = unwind["nounwind_abi"].get("AbortUnwindingCalls_before")
    st_a = unwind["nounwind_abi"].get("AbortUnwindingCalls_after")
    r = find_run(unwind["nounwind_abi"]["runs"], 1)
    add(
        "nounwind_abi::resume_rewritten_and_cleanup_still_runs",
        st_b is not None
        and st_a is not None
        and st_b["resume_terminators"] >= 1
        and st_a["resume_terminators"] == 0
        and st_a["terminate_terminators"] >= 1
        and r["stdout"] == ["drop g"]
        and r["signal"] == "SIGABRT",
        f"resume before/after = {st_b and st_b['resume_terminators']}/{st_a and st_a['resume_terminators']}, "
        f"terminate after = {st_a and st_a['terminate_terminators']}, stdout = {r['stdout']}, signal = {r['signal']}",
    )

    # 11. Hand-written MIR: the join lowered without a flag.
    ra = find_run(custom["join_no_flag_always_drop"]["runs"], 1)
    rn = find_run(custom["join_no_flag_never_drop"]["runs"], 0)
    rr = [find_run(custom["join_reference"]["runs"], a)["drop_counts"].get("x", 0) for a in (0, 1)]
    add("custom_mir::no_flag_always_drop_runs_destructor_twice", ra["drop_counts"].get("x", 0) == 2, str(ra["stdout"]))
    add("custom_mir::no_flag_never_drop_leaks", rn["drop_counts"].get("x", 0) == 0, str(rn["stdout"]))
    add("custom_mir::real_pass_inserts_flag_exactly_once", rr == [1, 1], f"destructor runs for x with argument 0/1 = {rr}")

    # 12. Hand-written MIR: a drop followed by a second drop of the same place at a join.
    rs1 = find_run(custom["stale_flag_join"]["runs"], 1)
    rc1 = find_run(custom["stale_flag_join_storage_dead"]["runs"], 1)
    add(
        "custom_mir::stale_flag_join_runs_destructor_twice",
        rs1["drop_counts"].get("x", 0) == 2 and len(custom["stale_flag_join"]["flag_locals"]) == 1,
        f"stdout = {rs1['stdout']}, flags = {custom['stale_flag_join']['flag_locals']}",
    )
    add(
        "custom_mir::storage_dead_clears_flag",
        rc1["drop_counts"].get("x", 0) == 1,
        f"stdout = {rc1['stdout']}",
    )

    # 13. Hand-written MIR: `UnwindContinue` on a cleanup-block drop is refused by the compiler.
    inv = results["invalid_custom_mir"]
    add(
        "custom_mir::continue_in_cleanup_rejected",
        inv["exit_code"] != 0 and inv["validator_message_found"],
        f"rustc exit = {inv['exit_code']}, message found = {inv['validator_message_found']}",
    )
    return checks


# --------------------------------------------------------------------------- main


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rustc", default="rustc")
    ap.add_argument("--out", default=str(HERE / "probe_output"))
    ap.add_argument("--keep-work", action="store_true", help="print the scratch directory instead of deleting it")
    args = ap.parse_args(argv)

    out_dir = Path(args.out).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    mir_out = out_dir / "mir"
    if mir_out.exists():
        shutil.rmtree(mir_out)
    mir_out.mkdir()

    rc, vv, _ = run([args.rustc, "-Vv"])
    if rc != 0:
        print("cannot run rustc -Vv", file=sys.stderr)
        return 2
    version = dict(
        line.split(": ", 1) for line in vv.splitlines()[1:] if ": " in line
    )
    version["version_line"] = vv.splitlines()[0]

    results = {
        "schema": "drop-elaboration-probe/1",
        "generated_on": datetime.date.today().isoformat(),
        "rustc": version,
        "dump_filter": DUMP_FILTER,
        "specimen_sha256": {
            name: sha256_of(SPECIMEN_DIR / name) for name in (MAIN_FILE, CUSTOM_FILE, INVALID_FILE)
        },
        "configurations": {},
    }

    with tempfile.TemporaryDirectory(prefix="drop_elab_probe_") as tmp:
        work = Path(tmp)
        plan = [
            ("panic_unwind", MAIN_FILE, "unwind"),
            ("panic_abort", MAIN_FILE, "abort"),
            ("custom_mir_unwind", CUSTOM_FILE, "unwind"),
        ]
        for label, fname, panic in plan:
            src = SPECIMEN_DIR / fname
            comp = compile_file(args.rustc, src, work, panic, [])
            cfg = {"source": f"support/specimens/{fname}", "compile_command": comp["command"], "compile_exit_code": comp["exit_code"], "functions": {}}
            if comp["binary"] is None:
                cfg["compile_stderr_excerpt"] = comp["stderr_excerpt"]
                results["configurations"][label] = cfg
                continue
            names = specimen_names(src)
            dumps = collect_function_dumps(comp["dump_dir"], src.stem)
            for fn in sorted(set(names) | (EXTRA_ANALYSED & set(dumps))):
                # Only the specimen functions (and the generic helper they call) are analysed;
                # `main`, constructors, closures and promoted constants are skipped.
                analysed = analyse_function(dumps.get(fn, {}))
                if fn in names:
                    analysed["runs"] = [run_specimen(comp["binary"], fn, a) for a in (0, 1)]
                cfg["functions"][fn] = analysed
                if label == "panic_abort" and fn != "nounwind_abi":
                    # Statistics only: the dumps around `ElaborateDrops` match the unwind
                    # configuration (see the `panic_abort::same_elaboration_as_unwind` check).
                    continue
                dest = mir_out / label
                dest.mkdir(exist_ok=True)
                for dump_name in ("ElaborateDrops.before", "ElaborateDrops.after", "runtime-post-cleanup.after"):
                    if dump_name in dumps.get(fn, {}) and (analysed["elaborate_drops_dumped"] != (dump_name == "runtime-post-cleanup.after")):
                        shutil.copyfile(dumps[fn][dump_name], dest / f"{fn}.{dump_name}.mir")
                if fn == "nounwind_abi":
                    for dump_name in ("AbortUnwindingCalls.before", "AbortUnwindingCalls.after"):
                        if dump_name in dumps[fn]:
                            shutil.copyfile(dumps[fn][dump_name], dest / f"{fn}.{dump_name}.mir")
            totals = {"functions": sum(1 for d in cfg["functions"].values() if d["elaborate_drops_dumped"]), "flag_locals": 0, "blocks_pre": 0, "blocks_post": 0,
                      "cleanup_blocks_pre": 0, "cleanup_blocks_post": 0, "drops_pre": 0, "drops_post": 0,
                      "flag_tests": 0, "flag_writes": 0, "styles": {}}
            for data in cfg["functions"].values():
                if not data["elaborate_drops_dumped"]:
                    continue
                totals["flag_locals"] += len(data["flag_locals"])
                totals["blocks_pre"] += data["pre_elaborate_drops"]["blocks"]
                totals["blocks_post"] += data["post_elaborate_drops"]["blocks"]
                totals["cleanup_blocks_pre"] += data["pre_elaborate_drops"]["cleanup_blocks"]
                totals["cleanup_blocks_post"] += data["post_elaborate_drops"]["cleanup_blocks"]
                totals["drops_pre"] += data["pre_elaborate_drops"]["drop_terminators"]
                totals["drops_post"] += data["post_elaborate_drops"]["drop_terminators"]
                totals["flag_tests"] += data["post_elaborate_drops"]["flag_tests"]
                totals["flag_writes"] += sum(data["post_elaborate_drops"]["flag_writes"].values())
                for k, v in data["style_counts"].items():
                    totals["styles"][k] = totals["styles"].get(k, 0) + v
            cfg["totals"] = totals
            results["configurations"][label] = cfg

        # The deliberately ill-formed hand-written body.
        inv_src = SPECIMEN_DIR / INVALID_FILE
        inv = compile_file(args.rustc, inv_src, work, "unwind", [])
        inv_run = None
        if inv["binary"] is not None:
            inv_run = run_specimen(inv["binary"], None, None)
        rc2, _, err2 = run(
            [args.rustc, "--edition", "2021", "-C", "panic=unwind", "-C", "opt-level=0", str(inv_src), "-o", str(work / "inv2.bin")],
            cwd=work,
            env=dict(os.environ, RUSTC_ICE="0", RUST_BACKTRACE="0"),
        )
        message = "`UnwindAction::Continue` in cleanup block"
        results["invalid_custom_mir"] = {
            "source": f"support/specimens/{INVALID_FILE}",
            "compile_command": inv["command"],
            "exit_code": inv["exit_code"],
            "validator_message": message,
            "validator_message_found": message in err2,
            "broken_mir_line": next((line.strip() for line in err2.splitlines() if "broken MIR" in line), None),
            "run": inv_run,
        }
        if results["invalid_custom_mir"]["broken_mir_line"]:
            results["invalid_custom_mir"]["broken_mir_line"] = re.sub(
                r"/rustc-dev/[0-9a-f]{40}/", "<rustc-src>/", results["invalid_custom_mir"]["broken_mir_line"]
            )
        if args.keep_work:
            kept = Path(tempfile.gettempdir()) / "drop_elab_probe_kept"
            if kept.exists():
                shutil.rmtree(kept)
            shutil.copytree(work, kept)
            print(f"scratch copy kept at {kept}")

    results["checks"] = evaluate_checks(results)
    failed = [c for c in results["checks"] if not c["pass"]]
    results["checks_passed"] = len(results["checks"]) - len(failed)
    results["checks_failed"] = len(failed)

    (out_dir / "probe_results.json").write_text(json.dumps(results, indent=1, sort_keys=True) + "\n")
    write_summary(results, out_dir / "probe_summary.md")
    print(f"wrote {out_dir / 'probe_results.json'}")
    print(f"checks: {results['checks_passed']} passed, {results['checks_failed']} failed")
    for c in failed:
        print(f"FAILED {c['check']}: {c['detail']}", file=sys.stderr)
    return 1 if failed else 0


def write_summary(results: dict, path: Path) -> None:
    lines = []
    lines.append("# Drop-elaboration probe summary")
    lines.append("")
    lines.append(f"- compiler: `{results['rustc']['version_line']}` (commit `{results['rustc'].get('commit-hash')}`, host `{results['rustc'].get('host')}`, LLVM `{results['rustc'].get('LLVM version')}`)")
    lines.append(f"- generated on: {results['generated_on']}")
    lines.append(f"- checks: {results['checks_passed']} passed, {results['checks_failed']} failed")
    lines.append("")
    for label, cfg in results["configurations"].items():
        lines.append(f"## {label} (`{cfg['source']}`)")
        lines.append("")
        if "totals" not in cfg:
            lines.append(f"compile failed with exit code {cfg['compile_exit_code']}")
            lines.append("")
            continue
        t = cfg["totals"]
        lines.append(
            f"Totals over {t['functions']} functions: flag locals {t['flag_locals']}; blocks {t['blocks_pre']} -> {t['blocks_post']}; "
            f"cleanup blocks {t['cleanup_blocks_pre']} -> {t['cleanup_blocks_post']}; drop terminators {t['drops_pre']} -> {t['drops_post']}; "
            f"flag tests {t['flag_tests']}; flag writes {t['flag_writes']}; styles {json.dumps(t['styles'], sort_keys=True)}."
        )
        lines.append("")
        lines.append("| function | flags | blocks pre→post | cleanup pre→post | drops pre→post | flag tests | flag writes T/F | styles | blocks at runtime-post-cleanup |")
        lines.append("| :-- | --: | :-- | :-- | :-- | --: | :-- | :-- | --: |")
        for fn, d in sorted(cfg["functions"].items()):
            if not d["elaborate_drops_dumped"]:
                lines.append(f"| `{fn}` | (runtime-dialect body: `ElaborateDrops` does not run) | | | | | | | |")
                continue
            pre, post = d["pre_elaborate_drops"], d["post_elaborate_drops"]
            rpc = d.get("runtime_post_cleanup_after")
            lines.append(
                f"| `{fn}` | {len(d['flag_locals'])} | {pre['blocks']}→{post['blocks']} | {pre['cleanup_blocks']}→{post['cleanup_blocks']} | "
                f"{pre['drop_terminators']}→{post['drop_terminators']} | {post['flag_tests']} | {post['flag_writes']['true']}/{post['flag_writes']['false']} | "
                f"{json.dumps(d['style_counts'], sort_keys=True)} | {rpc['blocks'] if rpc else 'n/a'} |"
            )
        lines.append("")
        lines.append("| function | arg | stdout | exit | signal | panics | runtime markers |")
        lines.append("| :-- | --: | :-- | --: | :-- | --: | :-- |")
        for fn, d in sorted(cfg["functions"].items()):
            for r in d.get("runs", []):
                lines.append(
                    f"| `{fn}` | {r['argument']} | `{'; '.join(r['stdout'])}` | {r['exit_code']} | {r['signal']} | {r['panic_count']} | {'; '.join(r['runtime_markers'])} |"
                )
        lines.append("")
    inv = results["invalid_custom_mir"]
    lines.append("## Ill-formed hand-written body")
    lines.append("")
    lines.append(f"- source: `{inv['source']}`")
    lines.append(f"- compiler exit code: {inv['exit_code']}")
    lines.append(f"- compiler message: `{inv['broken_mir_line']}`")
    lines.append("")
    lines.append("## Checks")
    lines.append("")
    lines.append("| check | result | measured |")
    lines.append("| :-- | :-- | :-- |")
    for c in results["checks"]:
        detail = c["detail"].replace("|", "\\|")
        lines.append(f"| `{c['check']}` | {'pass' if c['pass'] else 'FAIL'} | {detail} |")
    lines.append("")
    path.write_text("\n".join(lines))


if __name__ == "__main__":
    raise SystemExit(main())
