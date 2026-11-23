#!/usr/bin/env python3
"""Reproducible empirical probe for rustc InstrumentCoverage.

Compiles a multi-scenario Rust program under both `-Zmir-opt-level=0` and
`-Copt-level=2` with `-Cinstrument-coverage`, captures MIR dumps
(`InstrumentCoverage`, `CleanupPostBorrowck`), emits LLVM IR (`--emit=llvm-ir`),
decodes `@__covrec_*` `__llvm_covfun` counter expressions directly from the IR,
executes the instrumented binary, merges `.profraw` via `llvm-profdata`, and
collects `llvm-profdata show`, `llvm-cov export`, and `llvm-cov show` results.

All paths in JSON output are normalized relative to `<tmp>` / `<toolchain>`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

RUST_SRC = r'''#![feature(coroutines, coroutine_trait, coverage_attribute, stmt_expr_attributes)]

use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

macro_rules! check_step {
    ($val:expr, $limit:expr) => {{
        if $val > $limit {
            $val - $limit
        } else {
            $val + 1
        }
    }};
}

#[inline(never)]
pub fn diamond_and_nested_loop(n: u32, flag: bool) -> u32 {
    let mut acc = if flag { 10 } else { 20 };
    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < i {
            if (i + j) % 3 == 0 {
                acc += j;
            } else {
                acc ^= i;
            }
            j += 1;
        }
        if acc > 500 {
            break;
        }
        i += 1;
    }
    acc
}

#[inline(never)]
fn checked_div(a: u32, b: u32) -> Result<u32, &'static str> {
    if b == 0 {
        return Err("div_by_zero");
    }
    Ok(a / b)
}

#[inline(never)]
pub fn fallible_and_panic_paths(x: u32, y: u32) -> Result<u32, &'static str> {
    assert!(x < 10_000, "x too large");
    let q1 = checked_div(x, y)?;
    let q2 = checked_div(q1 + 10, y.saturating_add(1))?;
    if q2 == 999 {
        panic!("sentinel");
    }
    Ok(q1 + q2)
}

#[inline(never)]
fn may_panic_step(do_panic: bool, v: u32) -> u32 {
    if do_panic {
        panic!("mid_bcb_boom");
    }
    v + 7
}

#[inline(never)]
fn post_call_marker(v: u32) -> u32 {
    v.wrapping_mul(3)
}

#[inline(never)]
pub fn unwind_mid_bcb(do_panic: bool, v: u32) -> u32 {
    let a = may_panic_step(do_panic, v);
    let b = post_call_marker(a);
    b + 1
}

#[inline(never)]
pub fn unwind_underflow_loop(n: u32, flag: bool, do_panic: bool) -> u32 {
    let mut acc = if flag { may_panic_step(do_panic, 1) } else { 20 };
    let mut i = 0;
    while i < n {
        acc += i;
        i += 1;
    }
    acc
}

#[inline(never)]
pub fn unwind_loop_deficit(iters_before_panic: u32, panic_at: u32) -> u32 {
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < iters_before_panic {
        if i == panic_at {
            panic!("loop_unwind_boom");
        }
        if i % 2 == 0 {
            acc = acc.wrapping_add(i + 1);
        } else {
            acc = acc.wrapping_add(3);
        }
        i += 1;
    }
    acc
}

#[inline(never)]
pub fn macro_and_match_spans(v: i32) -> i32 {
    let adjusted = check_step!(v, 5);
    match adjusted {
        x if x < 0 => -x,
        y @ 0..=4 => {
            let tmp = y * 2;
            tmp + 1
        }
        5 | 6 => 42,
        other => other - 3,
    }
}

#[inline(never)]
pub fn opt_pruned_branch(x: u32) -> u32 {
    let flag = false;
    if flag {
        x.wrapping_mul(17)
    } else {
        x.wrapping_add(5)
    }
}

#[inline(never)]
pub fn inescapable_branch(take_exit: bool, x: u32) -> u32 {
    if take_exit {
        x + 1
    } else {
        let mut s = x;
        loop {
            s = s.wrapping_add(1);
            if s == u32::MAX && !take_exit && std::hint::black_box(false) {
                continue;
            }
        }
    }
}

#[inline(never)]
pub fn coroutine_yield_once(stop_early: bool) -> i32 {
    let mut gen_obj = #[coroutine]
    |mut x: i32| {
        yield x + 1;
        x += 10;
        yield x + 2;
        x + 100
    };
    let mut total = 0;
    match Pin::new(&mut gen_obj).resume(5) {
        CoroutineState::Yielded(v) => total += v,
        CoroutineState::Complete(v) => total += v,
    }
    if !stop_early {
        match Pin::new(&mut gen_obj).resume(0) {
            CoroutineState::Yielded(v) => total += v,
            CoroutineState::Complete(v) => total += v,
        }
    }
    total
}

#[inline(never)]
pub const fn ctfe_and_runtime(x: u32) -> u32 {
    if x > 10 { x - 10 } else { x + 10 }
}

const CTFE_VAL: u32 = ctfe_and_runtime(25);

#[coverage(off)]
fn run_catch_unwind_silently<F: FnOnce() -> u32 + std::panic::UnwindSafe>(f: F) -> Option<u32> {
    std::panic::catch_unwind(f).ok()
}

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let a = diamond_and_nested_loop(5, true) + diamond_and_nested_loop(2, false);
    let b = fallible_and_panic_paths(20, 4).unwrap_or(0)
        + fallible_and_panic_paths(20, 0).unwrap_or(7);
    let u1 = run_catch_unwind_silently(|| unwind_mid_bcb(true, 4)).unwrap_or(99);
    let u2 = run_catch_unwind_silently(|| unwind_underflow_loop(3, true, true)).unwrap_or(88);
    let u3 = run_catch_unwind_silently(|| unwind_loop_deficit(5, 3)).unwrap_or(77);
    let c = macro_and_match_spans(-2)
        + macro_and_match_spans(3)
        + macro_and_match_spans(10);
    let o = opt_pruned_branch(12);
    let e = inescapable_branch(true, 4);
    let g = coroutine_yield_once(true);
    let k = CTFE_VAL + ctfe_and_runtime(4);
    println!("COV={a},{b},{u1},{u2},{u3},{c},{o},{e},{g},{k}");
}
'''


def find_tools() -> tuple[str, str, str]:
    rustc = os.environ.get("RUSTC") or str(Path.home() / ".cargo" / "bin" / "rustc")
    if not Path(rustc).exists():
        rustc = "rustc"
    sysroot = subprocess.check_output([rustc, "--print", "sysroot"], text=True).strip()
    vv = subprocess.check_output([rustc, "-vV"], text=True)
    host = next(
        line.split(": ", 1)[1].strip()
        for line in vv.splitlines()
        if line.startswith("host:")
    )
    llvm_bin = Path(sysroot) / "lib" / "rustlib" / host / "bin"
    return rustc, str(llvm_bin / "llvm-profdata"), str(llvm_bin / "llvm-cov")


def sanitize_text(text: str, tmp_dir: Path, sysroot: str) -> str:
    text = text.replace(str(tmp_dir), "<tmp>")
    text = text.replace(sysroot, "<toolchain>")
    return text


def parse_llvm_c_string(escaped: str) -> bytes:
    out = bytearray()
    i = 0
    while i < len(escaped):
        ch = escaped[i]
        if ch == "\\" and i + 2 < len(escaped):
            hx = escaped[i + 1 : i + 3]
            if all(c in "0123456789ABCDEFabcdef" for c in hx):
                out.append(int(hx, 16))
                i += 3
                continue
        out.append(ord(ch))
        i += 1
    return bytes(out)


def decode_uleb128(buf: bytes, pos: int) -> tuple[int, int]:
    val = 0
    shift = 0
    while pos < len(buf):
        b = buf[pos]
        pos += 1
        val |= (b & 0x7F) << shift
        if (b & 0x80) == 0:
            return val, pos
        shift += 7
    raise ValueError("truncated ULEB128")


def decode_covfun_payload(buf: bytes) -> dict[str, Any]:
    pos = 0
    n_files, pos = decode_uleb128(buf, pos)
    file_map = []
    for _ in range(n_files):
        fid, pos = decode_uleb128(buf, pos)
        file_map.append(fid)

    n_exprs, pos = decode_uleb128(buf, pos)
    raw_exprs = []
    for _ in range(n_exprs):
        lhs_raw, pos = decode_uleb128(buf, pos)
        rhs_raw, pos = decode_uleb128(buf, pos)
        raw_exprs.append((lhs_raw, rhs_raw))

    expr_ops: dict[int, str] = {}

    def record_ref(raw_val: int) -> dict[str, Any]:
        tag = raw_val & 0x3
        cid = raw_val >> 2
        if tag == 0:
            return {"kind": "Zero", "id": 0}
        if tag == 1:
            return {"kind": "Counter", "id": cid}
        op = "Subtract" if tag == 2 else "Add"
        expr_ops[cid] = op
        return {"kind": "Expression", "id": cid, "op": op}

    for lhs_raw, rhs_raw in raw_exprs:
        record_ref(lhs_raw)
        record_ref(rhs_raw)

    regions_by_file = []
    for file_idx in range(n_files):
        n_regs, pos = decode_uleb128(buf, pos)
        prev_line = 0
        file_regs = []
        for _ in range(n_regs):
            hdr, pos = decode_uleb128(buf, pos)
            low2 = hdr & 0x3
            exp_bit = (hdr >> 2) & 0x1
            kind_str = "Code"
            extra: dict[str, Any] = {}
            if low2 != 0 or exp_bit == 0:
                if low2 == 0 and (hdr >> 3) != 0:
                    rkind = hdr >> 3
                    if rkind == 2:
                        kind_str = "Skipped"
                    elif rkind == 4:
                        kind_str = "Branch"
                        t_raw, pos = decode_uleb128(buf, pos)
                        f_raw, pos = decode_uleb128(buf, pos)
                        extra = {"true": record_ref(t_raw), "false": record_ref(f_raw)}
                    else:
                        kind_str = f"Kind{rkind}"
                else:
                    extra = {"counter": record_ref(hdr)}
            else:
                kind_str = "Expansion"
                extra = {"expanded_file_id": hdr >> 3}
            d_line_start, pos = decode_uleb128(buf, pos)
            col_start, pos = decode_uleb128(buf, pos)
            d_line_end, pos = decode_uleb128(buf, pos)
            col_end, pos = decode_uleb128(buf, pos)
            line_start = prev_line + d_line_start
            line_end = line_start + d_line_end
            prev_line = line_start
            is_gap = bool(col_end & (1 << 31))
            col_end_clean = col_end & ~(1 << 31)
            file_regs.append({
                "kind": kind_str,
                "gap": is_gap,
                "span": [line_start, col_start, line_end, col_end_clean],
                **extra,
            })
        regions_by_file.append({
            "local_file_id": file_idx,
            "global_file_id": file_map[file_idx],
            "regions": file_regs,
        })

    exprs_decoded = []
    for idx, (lhs_raw, rhs_raw) in enumerate(raw_exprs):
        exprs_decoded.append({
            "id": idx,
            "op": expr_ops.get(idx, "Unreferenced"),
            "lhs": record_ref(lhs_raw),
            "rhs": record_ref(rhs_raw),
        })

    def fmt_term(t: dict[str, Any], depth: int = 0) -> str:
        if t["kind"] == "Zero":
            return "0"
        if t["kind"] == "Counter":
            return f"c{t['id']}"
        if depth > 12 or t["id"] >= len(exprs_decoded):
            return f"e{t['id']}"
        e = exprs_decoded[t["id"]]
        sym = "+" if e["op"] == "Add" else "-"
        return f"({fmt_term(e['lhs'], depth + 1)} {sym} {fmt_term(e['rhs'], depth + 1)})"

    for e in exprs_decoded:
        sym = "+" if e["op"] == "Add" else "-" if e["op"] == "Subtract" else "?"
        e["pretty"] = f"{fmt_term(e['lhs'])} {sym} {fmt_term(e['rhs'])}"

    return {
        "virtual_file_mapping": file_map,
        "expressions": exprs_decoded,
        "regions_by_file": regions_by_file,
        "decoded_bytes": pos,
        "total_bytes": len(buf),
    }


def extract_llvm_ir_info(ll_text: str) -> dict[str, Any]:
    profc_arrays: dict[str, int] = {}
    for m in re.finditer(
        r"@(__profc_([A-Za-z0-9_]+))\s*=\s*private global \[(\d+) x i64\]",
        ll_text,
    ):
        profc_arrays[m.group(2)] = int(m.group(3))

    profd_hash_to_name: dict[str, str] = {}
    for m in re.finditer(
        r"@__profd_([A-Za-z0-9_]+)\s*=\s*private global \{[^}]*\}\s*\{\s*i64\s*(-?\d+),",
        ll_text,
    ):
        mangled, val = m.group(1), int(m.group(2))
        profd_hash_to_name[f"{val & ((1 << 64) - 1):X}"] = mangled

    atomicrmw_by_fn: dict[str, list[str]] = {}
    for line in ll_text.splitlines():
        if "atomicrmw add ptr" in line and "@__profc_" in line:
            m = re.search(r"@__profc_([A-Za-z0-9_]+)", line)
            if m:
                atomicrmw_by_fn.setdefault(m.group(1), []).append(line.strip())

    covfun_records: dict[str, Any] = {}
    for m in re.finditer(
        r'@(__covrec_([0-9A-Fa-f]+)(u?))\s*=.*?\[(\d+) x i8\]\s*c"([^"]+)"',
        ll_text,
    ):
        sym, hx, used_flag, size_str, esc = m.groups()
        decoded = decode_covfun_payload(parse_llvm_c_string(esc))
        mangled = profd_hash_to_name.get(hx, f"unknown_{hx}")
        covfun_records[mangled] = {
            "covrec_symbol": sym,
            "name_hash_hex": hx,
            "is_used": used_flag == "u",
            "payload_bytes": int(size_str),
            "decoded": decoded,
        }

    return {
        "profc_lengths": profc_arrays,
        "atomicrmw_by_fn": atomicrmw_by_fn,
        "covfun_records": covfun_records,
    }


def parse_profdata_counts(prof_txt: str) -> dict[str, Any]:
    out: dict[str, Any] = {}
    curr: str | None = None
    for raw in prof_txt.splitlines():
        line = raw.strip()
        if line.endswith(":") and line != "Counters:":
            curr = line[:-1]
            out[curr] = {"counters": 0, "function_count": None, "block_counts": []}
        elif curr is not None:
            if line.startswith("Hash:"):
                out[curr]["hash"] = line.split(":", 1)[1].strip()
            elif line.startswith("Counters:"):
                out[curr]["counters"] = int(line.split(":", 1)[1].strip())
            elif line.startswith("Function count:"):
                out[curr]["function_count"] = int(line.split(":", 1)[1].strip())
            elif line.startswith("Block counts:"):
                arr = line.split(":", 1)[1].strip()
                out[curr]["block_counts"] = json.loads(arr)
                curr = None
    return out


def eval_decoded_covfun(
    decoded: dict[str, Any], raw_counts: list[int]
) -> list[dict[str, Any]]:
    """Independently evaluate LLVM CounterExpression DAG over 64-bit signed/unsigned wrap."""
    exprs = decoded["expressions"]

    def eval_term(term: dict[str, Any]) -> int:
        k = term["kind"]
        if k == "Zero":
            return 0
        if k == "Counter":
            cid = term["id"]
            return raw_counts[cid] if cid < len(raw_counts) else 0
        e = exprs[term["id"]]
        lhs = eval_term(e["lhs"])
        rhs = eval_term(e["rhs"])
        # Match LLVM CoverageMapping.cpp CounterMappingContext::evaluate (int64_t)
        # followed by CounterValues[C] = *ValueOrErr (uint64_t)
        res = (lhs - rhs) if e["op"] == "Subtract" else (lhs + rhs)
        # Convert signed 64-bit wrap to uint64_t:
        return res & ((1 << 64) - 1)

    out = []
    for rf in decoded["regions_by_file"]:
        for reg in rf["regions"]:
            if reg["kind"] == "Code":
                val = eval_term(reg["counter"])
                clamped = min(val, (1 << 63) - 1)
                out.append({
                    "span": reg["span"],
                    "raw_u64": val,
                    "json_clamped_i64": clamped,
                    "counter": reg["counter"],
                })
    return out


def extract_mir_coverage_summaries(
    mir_dir: Path, tmp_dir: Path, sysroot: str
) -> dict[str, Any]:
    targets = (
        "diamond_and_nested_loop",
        "fallible_and_panic_paths",
        "unwind_mid_bcb",
        "unwind_underflow_loop",
        "unwind_loop_deficit",
        "macro_and_match_spans",
        "opt_pruned_branch",
        "inescapable_branch",
        "coroutine_yield_once",
        "ctfe_and_runtime",
    )
    summaries: dict[str, Any] = {}
    for p in sorted(mir_dir.iterdir()):
        if not p.name.endswith(".mir"):
            continue
        if not any(t in p.name for t in targets):
            continue
        txt = sanitize_text(p.read_text(encoding="utf-8"), tmp_dir, sysroot)
        vcs = re.findall(r"Coverage::VirtualCounter\((bcb\d+)\)", txt)
        cov_spans = [
            ln.strip() for ln in txt.splitlines() if ln.strip().startswith("coverage ")
        ]
        # Store concise per-pass summary and full MIR for key functions
        key = p.name
        entry: dict[str, Any] = {
            "virtual_counters": vcs,
            "coverage_mapping_lines_count": len(cov_spans),
        }
        if (
            "InstrumentCoverage.after.mir" in p.name
            or "PreOptimizations.after.mir" in p.name
            or "ReorderLocals.after.mir" in p.name
        ):
            entry["coverage_mappings"] = cov_spans
            if any(
                k in p.name
                for k in (
                    "diamond_and_nested_loop",
                    "unwind_underflow_loop",
                    "opt_pruned_branch",
                    "coroutine_yield_once",
                )
            ):
                entry["mir_text"] = txt
        summaries[key] = entry
    return summaries


def run_profile(
    rustc: str,
    llvm_profdata: str,
    llvm_cov: str,
    sysroot: str,
    extra_flags: list[str],
    label: str,
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        src = tmp / "cov_probe.rs"
        src.write_text(RUST_SRC, encoding="utf-8")
        mir_dir = tmp / "mir"
        mir_dir.mkdir()
        exe = tmp / "cov_probe"
        ll = tmp / "cov_probe.ll"

        common = [
            rustc,
            "--edition",
            "2024",
            "-Cinstrument-coverage",
            *extra_flags,
            "--crate-name",
            "cov_probe",
        ]
        res_bin = subprocess.run(
            [
                *common,
                "-Zdump-mir=InstrumentCoverage|CleanupPostBorrowck|PreOptimizations|ReorderLocals",
                f"-Zdump-mir-dir={mir_dir}",
                "-o",
                str(exe),
                str(src),
            ],
            text=True,
            capture_output=True,
            check=True,
        )
        subprocess.run(
            [*common, "--emit=llvm-ir", "-o", str(ll), str(src)],
            text=True,
            capture_output=True,
            check=True,
        )

        profraw = tmp / "cov.profraw"
        res_run = subprocess.run(
            [str(exe)],
            env={**os.environ, "LLVM_PROFILE_FILE": str(profraw)},
            text=True,
            capture_output=True,
            check=True,
        )
        profdata = tmp / "cov.profdata"
        subprocess.run(
            [llvm_profdata, "merge", "-sparse", str(profraw), "-o", str(profdata)],
            check=True,
        )
        prof_txt = subprocess.check_output(
            [llvm_profdata, "show", "--all-functions", "--counts", str(profdata)],
            text=True,
        )
        cov_export = json.loads(
            subprocess.check_output(
                [llvm_cov, "export", str(exe), f"-instr-profile={profdata}"],
                text=True,
            )
        )
        cov_show = subprocess.check_output(
            [llvm_cov, "show", str(exe), f"-instr-profile={profdata}"],
            text=True,
        )

        ll_text = ll.read_text(encoding="utf-8")
        ir_info = extract_llvm_ir_info(ll_text)
        prof_parsed = parse_profdata_counts(prof_txt)

        # Cross-check independent covfun expression evaluation vs llvm-cov export
        focus_tokens = (
            "diamond_and_nested_loop",
            "fallible_and_panic_paths",
            "unwind_mid_bcb",
            "unwind_underflow_loop",
            "unwind_loop_deficit",
            "macro_and_match_spans",
            "opt_pruned_branch",
            "inescapable_branch",
            "coroutine_yield_once",
            "ctfe_and_runtime",
        )
        export_fns: dict[str, Any] = {}
        eval_cross_check: dict[str, Any] = {}
        for fn in cov_export["data"][0]["functions"]:
            fname = fn["name"]
            if not any(tok in fname for tok in focus_tokens):
                continue
            export_fns[fname] = {
                "count": fn["count"],
                "regions_count": len(fn["regions"]),
                "regions": fn["regions"],
            }
            if fname in ir_info["covfun_records"] and fname in prof_parsed:
                pinfo = prof_parsed[fname]
                raw_cnts = [pinfo["function_count"] or 0] + pinfo["block_counts"]
                re_eval = eval_decoded_covfun(
                    ir_info["covfun_records"][fname]["decoded"], raw_cnts
                )
                # Compare region counts by (lineStart, colStart, lineEnd, colEnd)
                exp_map = {
                    (r[0], r[1], r[2], r[3]): r[4] for r in fn["regions"]
                }
                mismatches = []
                for item in re_eval:
                    sp = tuple(item["span"])
                    if sp in exp_map and exp_map[sp] != item["json_clamped_i64"]:
                        mismatches.append({
                            "span": list(sp),
                            "decoded": item["json_clamped_i64"],
                            "llvm_cov_export": exp_map[sp],
                        })
                eval_cross_check[fname] = {
                    "raw_counters": raw_cnts,
                    "evaluated_regions": len(re_eval),
                    "mismatches": mismatches,
                    "max_raw_u64": max((x["raw_u64"] for x in re_eval), default=0),
                }

        # Filter IR info to focus functions
        ir_focus = {
            "profc_lengths": {
                k: v for k, v in ir_info["profc_lengths"].items()
                if any(tok in k for tok in focus_tokens)
            },
            "atomicrmw_counts": {
                k: len(v) for k, v in ir_info["atomicrmw_by_fn"].items()
                if any(tok in k for tok in focus_tokens)
            },
            "covfun_records": {
                k: v for k, v in ir_info["covfun_records"].items()
                if any(tok in k for tok in focus_tokens)
            },
        }

        return {
            "label": label,
            "flags": extra_flags,
            "compile_stderr": sanitize_text(res_bin.stderr, tmp, sysroot),
            "run_stdout": res_run.stdout.strip(),
            "llvm_cov_show": sanitize_text(cov_show, tmp, sysroot),
            "profdata_counts": {
                k: v for k, v in prof_parsed.items()
                if any(tok in k for tok in focus_tokens)
            },
            "llvm_cov_export_functions": export_fns,
            "ir_focus": ir_focus,
            "independent_covfun_eval_check": eval_cross_check,
            "mir_summaries": extract_mir_coverage_summaries(mir_dir, tmp, sysroot),
        }


def run_knuth_stevenson_reference_check() -> dict[str, Any]:
    """Run an independent Python BalancedFlowGraph + Knuth-Stevenson check."""
    # Exact 5-node example from rustc node_flow/tests.rs::example_driver
    edges = [(0, 1), (0, 3), (1, 0), (1, 2), (2, 1), (2, 4), (3, 3), (3, 4), (4, 0)]
    n = 5
    succs: list[list[int]] = [[] for _ in range(n)]
    for u, v in edges:
        succs[u].append(v)

    parent = list(range(n))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def unify(a: int, b: int) -> int:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra
        return find(ra)

    rep_succ = []
    for u in range(n):
        acc = succs[u][0]
        for v in succs[u][1:]:
            acc = unify(acc, v)
        rep_succ.append(acc)
    supernode = [find(i) for i in range(n)]
    succ_supernode = [supernode[s] for s in rep_succ]

    span_edges: list[dict[str, Any] | None] = [None] * n
    terms: list[list[tuple[str, int]]] = [[] for _ in range(n)]

    def root(x: int) -> int:
        while span_edges[x] is not None:
            x = span_edges[x]["parent"]
        return x

    def yank(x: int) -> None:
        path = [x]
        curr = x
        while span_edges[curr] is not None:
            curr = span_edges[curr]["parent"]
            path.append(curr)
        for i in range(len(path) - 2, -1, -1):
            a, b = path[i], path[i + 1]
            e = span_edges[a]
            span_edges[a] = None
            span_edges[b] = {
                "rev": not e["rev"],
                "claim": e["claim"],
                "parent": a,
            }

    priority_list = [3, 1, 2, 0, 4]
    for node in priority_list:
        sn = supernode[node]
        yank(sn)
        ssn = succ_supernode[node]
        if sn != root(ssn):
            span_edges[sn] = {"rev": False, "claim": node, "parent": ssn}
        else:
            terms[node].append(("+", node))
            curr = ssn
            while curr != sn:
                e = span_edges[curr]
                op = "-" if e["rev"] else "+"
                terms[e["claim"]].append((op, node))
                curr = e["parent"]

    formatted = [
        f"[{i}]: "
        + " ".join(
            f"{op}c{nid}" for op, nid in sorted(terms[i], key=lambda x: x[1])
        )
        for i in range(n)
    ]
    expected = [
        "[0]: +c0",
        "[1]: +c0 +c2 -c4",
        "[2]: +c2",
        "[3]: +c3",
        "[4]: +c4",
    ]
    assert formatted == expected, f"Mismatch: {formatted} != {expected}"
    # Verify Kirchhoff reconstruction on concrete balanced flows (cycle sums)
    # Valid circulation on edges: e(0,1)=2, e(0,3)=5, e(1,0)=1, e(1,2)=4,
    # e(2,1)=3, e(2,4)=1, e(3,3)=7, e(3,4)=5, e(4,0)=6 ->
    # node flows: f0=7, f1=5, f2=4, f3=12, f4=6
    f = [7, 5, 4, 12, 6]
    reconstructed = []
    for i in range(n):
        val = sum(f[nid] if op == "+" else -f[nid] for op, nid in terms[i])
        reconstructed.append(val)
    assert reconstructed == f, f"{reconstructed} != {f}"
    return {
        "example": "knuth_stevenson_1973_node_flow_test",
        "priority_list": priority_list,
        "formatted_terms": formatted,
        "sample_balanced_flow": f,
        "reconstructed_flow": reconstructed,
        "exact_match": reconstructed == f,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, help="Optional JSON output file")
    args = parser.parse_args()

    rustc, llvm_profdata, llvm_cov = find_tools()
    sysroot = subprocess.check_output([rustc, "--print", "sysroot"], text=True).strip()
    rustc_vv = subprocess.check_output([rustc, "-vV"], text=True).strip()
    profdata_ver = subprocess.check_output([llvm_profdata, "--version"], text=True).strip()
    cov_ver = subprocess.check_output([llvm_cov, "--version"], text=True).strip()

    ks_check = run_knuth_stevenson_reference_check()
    p_mir0 = run_profile(
        rustc, llvm_profdata, llvm_cov, sysroot, ["-Zmir-opt-level=0", "-Copt-level=0"], "mir_opt_0"
    )
    p_opt2 = run_profile(
        rustc, llvm_profdata, llvm_cov, sysroot, ["-Copt-level=2"], "opt_level_2"
    )

    result = {
        "probe_id": "probe-coverage-kirchhoff-node-flow-and-spans",
        "toolchain": {
            "rustc_vv": rustc_vv,
            "llvm_profdata_version": profdata_ver,
            "llvm_cov_version": cov_ver,
        },
        "source_program": RUST_SRC,
        "knuth_stevenson_reference_check": ks_check,
        "profiles": {
            "mir_opt_0": p_mir0,
            "opt_level_2": p_opt2,
        },
    }

    encoded = json.dumps(result, indent=2, ensure_ascii=True)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(encoded + "\n", encoding="utf-8")
        print(f"Wrote {args.out} ({len(encoded)} bytes)")
    else:
        print(encoded[:2000])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
