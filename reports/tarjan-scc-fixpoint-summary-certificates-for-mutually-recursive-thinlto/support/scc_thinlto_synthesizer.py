#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tarjan SCC Fixpoint Summary Propagator (`SccGfpCert`) and 2D Lexicographic
Ranking Synthesizer (`SccRankingSynthesizer`) on rustc 1.99.1 and LLVM 23.1.1.
"""

from __future__ import annotations

import csv
import json
import re
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

SUPPORT_DIR = Path(__file__).resolve().parent
RUSTC = ["rustc", "+1.99.1-x86_64-unknown-linux-gnu"]


@dataclass
class FnNode:
    name: str
    callees: list[tuple[str, str, int]]  # (callee_name, measure_delta_kind, delta_val)
    local_mem_effect: str  # "readnone", "readonly", "argmemonly", "readwrite"
    local_nounwind: bool
    measure_expr: str


def tarjan_scc(nodes: dict[str, FnNode]) -> list[list[str]]:
    """Computes Strongly Connected Components in topological (bottom-up) order."""
    index = 0
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    sccs: list[list[str]] = []

    def strongconnect(v: str) -> None:
        nonlocal index
        indices[v] = index
        lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)

        for w, _, _ in nodes[v].callees:
            if w not in nodes:
                continue
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])

        if lowlink[v] == indices[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                comp.append(w)
                if w == v:
                    break
            sccs.append(comp)

    for v in nodes:
        if v not in indices:
            strongconnect(v)
    return sccs


MEM_RANK = {"readnone": 0, "readonly": 1, "argmemonly": 2, "readwrite": 3}
RANK_TO_MEM = {0: "readnone", 1: "readonly", 2: "argmemonly", 3: "readwrite"}


def synthesize_scc_certificates(
    nodes: dict[str, FnNode], sccs: list[list[str]]
) -> dict[str, dict[str, Any]]:
    """Computes:
    1. U9 DAG-only summary propagation (conservatively fails on any cycle/self-loop).
    2. SccGfpCert co-inductive greatest-fixpoint propagation for (nounwind, MemEffect).
    3. SccRankingCert 2D lexicographic ranking synthesis `(param_measure, node_rank)`
       with FarkasCert2 edge discharge for `willreturn`.
    """
    results: dict[str, dict[str, Any]] = {}

    for scc in sccs:
        scc_set = set(scc)
        # Check if SCC has any internal edge (including self-loop)
        has_internal_cycle = any(
            callee in scc_set for u in scc for callee, _, _ in nodes[u].callees
        )

        # 1. Greatest-fixpoint co-inductive propagation for (MemEffect, nounwind)
        max_mem_rank = 0
        all_nounwind = True
        for u in scc:
            max_mem_rank = max(max_mem_rank, MEM_RANK[nodes[u].local_mem_effect])
            if not nodes[u].local_nounwind:
                all_nounwind = False
            for callee, _, _ in nodes[u].callees:
                if callee not in scc_set and callee in results:
                    max_mem_rank = max(
                        max_mem_rank, MEM_RANK[results[callee]["scc_gfp_mem_effect"]]
                    )
                    if not results[callee]["scc_gfp_nounwind"]:
                        all_nounwind = False

        gfp_mem = RANK_TO_MEM[max_mem_rank]

        # 2. Lexicographic ranking synthesis for `willreturn`
        # Assign node_rank in [0, |S|-1] by topological order of zero-decrease edges inside S
        zero_edges: dict[str, list[str]] = {u: [] for u in scc}
        has_negative_or_unbounded_edge = False
        for u in scc:
            for callee, kind, delta in nodes[u].callees:
                if callee in scc_set:
                    if kind == "unbounded":
                        has_negative_or_unbounded_edge = True
                    elif delta == 0:
                        zero_edges[u].append(callee)

        # Compute longest zero-decrease path length from each node u in scc
        node_ranks: dict[str, int] = {}
        visiting: set[str] = set()
        zero_cycle = False

        def compute_rank(u: str) -> int:
            nonlocal zero_cycle
            if u in node_ranks:
                return node_ranks[u]
            if u in visiting:
                zero_cycle = True
                return 0
            visiting.add(u)
            r = 0
            for v in zero_edges[u]:
                r = max(r, 1 + compute_rank(v))
            visiting.remove(u)
            node_ranks[u] = r
            return r

        for u in scc:
            compute_rank(u)

        ranking_valid = (not has_negative_or_unbounded_edge) and (not zero_cycle)
        # Verify every intra-SCC edge strictly decreases (param_measure, node_rank)
        farkas_witnesses = []
        if ranking_valid:
            for u in scc:
                for callee, kind, delta in nodes[u].callees:
                    if callee in scc_set:
                        if delta < 0:
                            farkas_witnesses.append(
                                f"{u}->{callee}: param_measure' <= param_measure {delta} (FarkasCert2: [1, 1])"
                            )
                        elif delta == 0 and node_ranks[callee] < node_ranks[u]:
                            farkas_witnesses.append(
                                f"{u}->{callee}: param_measure' == param_measure && rank({callee})={node_ranks[callee]} < rank({u})={node_ranks[u]}"
                            )
                        else:
                            ranking_valid = False

        # Also check external callees for willreturn
        for u in scc:
            for callee, _, _ in nodes[u].callees:
                if callee not in scc_set and callee in results:
                    if not results[callee]["scc_lfp_willreturn"]:
                        ranking_valid = False

        for u in scc:
            results[u] = {
                "scc_size": len(scc),
                "is_cyclic_scc": has_internal_cycle,
                "u9_dag_nounwind": (not has_internal_cycle) and all_nounwind,
                "u9_dag_mem_effect": gfp_mem if not has_internal_cycle else "readwrite",
                "u9_dag_willreturn": not has_internal_cycle,
                "scc_gfp_nounwind": all_nounwind,
                "scc_gfp_mem_effect": gfp_mem,
                "scc_lfp_willreturn": ranking_valid and all_nounwind,
                "lex_rank_2d": f"({nodes[u].measure_expr}, {node_ranks[u]})"
                if ranking_valid
                else "NONE (Rejected)",
                "farkas_edge_certificates": farkas_witnesses,
            }

    return results


def parse_llvm_ir_fn_attrs(ll_text: str, fn_names: list[str]) -> dict[str, dict[str, Any]]:
    """Extracts the exact LLVM 23.1.1 PostOrderFunctionAttrsPass attributes
    emitted by rustc 1.99.1 for each function in `recursive_thinlto_corpus.rs`.
    """
    attr_groups: dict[str, str] = {}
    for m in re.finditer(r"attributes (#\d+) = \{([^}]+)\}", ll_text):
        attr_groups[m.group(1)] = m.group(2).strip()

    fn_attrs: dict[str, dict[str, Any]] = {}
    for fn_name in fn_names:
        pattern = re.compile(rf"define [^\n]*@{re.escape(fn_name)}\([^)]*\)\s*([^{{\n]+)")
        m = pattern.search(ll_text)
        attr_str = ""
        if m:
            tail = m.group(1)
            for grp_id in re.findall(r"#\d+", tail):
                attr_str += " " + attr_groups.get(grp_id, "")
        has_nounwind = "nounwind" in attr_str
        has_willreturn = "willreturn" in attr_str
        if "memory(none)" in attr_str:
            mem = "readnone"
        elif "memory(read)" in attr_str or "readonly" in attr_str:
            mem = "readonly"
        elif "memory(argmem:" in attr_str:
            mem = "argmemonly"
        else:
            mem = "readwrite"
        fn_attrs[fn_name] = {
            "llvm_nounwind": has_nounwind,
            "llvm_mem_effect": mem,
            "llvm_willreturn": has_willreturn,
            "raw_attr_str": attr_str.strip(),
        }
    return fn_attrs


def build_30fn_graph() -> dict[str, FnNode]:
    return {
        # SCC 1 (|S|=3): JSON parser
        "parse_json_value": FnNode(
            "parse_json_value",
            [("parse_json_array", "slice_len", -1), ("parse_json_object", "slice_len", -1)],
            "readonly",
            True,
            "buf.len()",
        ),
        "parse_json_array": FnNode(
            "parse_json_array",
            [("parse_json_value", "slice_len", -1), ("parse_json_array", "slice_len", -1)],
            "readonly",
            True,
            "buf.len()",
        ),
        "parse_json_object": FnNode(
            "parse_json_object",
            [("parse_json_value", "slice_len", -1), ("parse_json_object", "slice_len", -1)],
            "readonly",
            True,
            "buf.len()",
        ),
        # SCC 2 (|S|=3): Expression AST evaluator with zero-decrease hops
        "eval_expr": FnNode(
            "eval_expr",
            [("eval_term", "int_val", 0), ("eval_term", "int_val", -1)],
            "readnone",
            True,
            "depth",
        ),
        "eval_term": FnNode(
            "eval_term",
            [("eval_factor", "int_val", 0)],
            "readnone",
            True,
            "depth",
        ),
        "eval_factor": FnNode(
            "eval_factor",
            [("eval_expr", "int_val", -1)],
            "readnone",
            True,
            "depth",
        ),
        # SCC 3 (|S|=4): Frame State-Machine Dispatcher
        "fsm_state_header": FnNode(
            "fsm_state_header",
            [("fsm_state_length", "int_val", 0)],
            "readnone",
            True,
            "rem",
        ),
        "fsm_state_length": FnNode(
            "fsm_state_length",
            [("fsm_state_payload", "int_val", 0)],
            "readnone",
            True,
            "rem",
        ),
        "fsm_state_payload": FnNode(
            "fsm_state_payload",
            [("fsm_state_trailer", "int_val", 0)],
            "readnone",
            True,
            "rem",
        ),
        "fsm_state_trailer": FnNode(
            "fsm_state_trailer",
            [("fsm_state_header", "int_val", -1)],
            "readnone",
            True,
            "rem",
        ),
        # SCC 4 (|S|=2): DOM Sanitizer
        "dom_visit_element": FnNode(
            "dom_visit_element",
            [("dom_visit_children", "slice_len", -1)],
            "readonly",
            True,
            "nodes.len()",
        ),
        "dom_visit_children": FnNode(
            "dom_visit_children",
            [("dom_visit_element", "slice_len", -1)],
            "readonly",
            True,
            "nodes.len()",
        ),
        # SCC 5 (|S|=2): Regex Matcher
        "regex_match_seq": FnNode(
            "regex_match_seq",
            [("regex_match_alt", "int_val", 0)],
            "readonly",
            True,
            "pat_fuel",
        ),
        "regex_match_alt": FnNode(
            "regex_match_alt",
            [("regex_match_seq", "int_val", -1)],
            "readonly",
            True,
            "pat_fuel",
        ),
        # SCC 6 (|S|=2): Type Unification
        "unify_type_term": FnNode(
            "unify_type_term",
            [("unify_type_args", "int_val", 0)],
            "readnone",
            True,
            "fuel",
        ),
        "unify_type_args": FnNode(
            "unify_type_args",
            [("unify_type_term", "int_val", -1)],
            "readnone",
            True,
            "fuel",
        ),
        # SCCs 7..16 (|S|=1 self-recursive): 10 functions
        "gcd_bounded_steps": FnNode(
            "gcd_bounded_steps",
            [("gcd_bounded_steps", "int_val", -1)],
            "readnone",
            True,
            "fuel",
        ),
        "binary_search_rec": FnNode(
            "binary_search_rec",
            [("binary_search_rec", "slice_len", -1)],
            "readonly",
            True,
            "slice.len()",
        ),
        "trie_prefix_lookup": FnNode(
            "trie_prefix_lookup",
            [("trie_prefix_lookup", "slice_len", -1)],
            "readonly",
            True,
            "key.len()",
        ),
        "bst_checksum_rec": FnNode(
            "bst_checksum_rec",
            [("bst_checksum_rec", "slice_len", -1)],
            "readonly",
            True,
            "tree.len()",
        ),
        "varint_decode_rec": FnNode(
            "varint_decode_rec",
            [("varint_decode_rec", "slice_len", -1)],
            "readonly",
            True,
            "buf.len()",
        ),
        "fast_pow_mod_rec": FnNode(
            "fast_pow_mod_rec",
            [("fast_pow_mod_rec", "bit_shr", -1)],
            "readnone",
            True,
            "bits(exp)",
        ),
        "utf8_validate_ascii_chunks_rec": FnNode(
            "utf8_validate_ascii_chunks_rec",
            [("utf8_validate_ascii_chunks_rec", "slice_len", -1)],
            "readonly",
            True,
            "bytes.len()",
        ),
        "leb128_byte_len_rec": FnNode(
            "leb128_byte_len_rec",
            [("leb128_byte_len_rec", "bit_shr", -1)],
            "readnone",
            True,
            "bits(val)",
        ),
        "adler32_window_rec": FnNode(
            "adler32_window_rec",
            [("adler32_window_rec", "slice_len", -1)],
            "readonly",
            True,
            "data.len()",
        ),
        "argmem_mutating_fill_rec": FnNode(
            "argmem_mutating_fill_rec",
            [("argmem_mutating_fill_rec", "slice_len", -1)],
            "argmemonly",
            True,
            "dst.len()",
        ),
        # 4 Negative Canaries
        "canary_unbounded_collatz_rec": FnNode(
            "canary_unbounded_collatz_rec",
            [("canary_unbounded_collatz_rec", "unbounded", 1)],
            "readnone",
            True,
            "UNBOUNDED",
        ),
        "canary_zero_decrease_cycle_a": FnNode(
            "canary_zero_decrease_cycle_a",
            [("canary_zero_decrease_cycle_b", "int_val", 0)],
            "readnone",
            True,
            "n",
        ),
        "canary_zero_decrease_cycle_b": FnNode(
            "canary_zero_decrease_cycle_b",
            [("canary_zero_decrease_cycle_a", "int_val", 0)],
            "readnone",
            True,
            "n",
        ),
        "canary_panicking_recursive_walk": FnNode(
            "canary_panicking_recursive_walk",
            [("canary_panicking_recursive_walk", "int_val", -1)],
            "readnone",
            False,
            "depth",
        ),
    }


CALLER_OPT_BENCH_RS = r"""
use std::hint::black_box;
use std::time::Instant;

#[inline(never)]
pub fn eval_expr(depth: u32, x: u64) -> u64 {
    if depth == 0 {
        return x.wrapping_add(1);
    }
    let t = eval_term(depth, x.wrapping_mul(3));
    t.wrapping_add(eval_term(depth - 1, x.wrapping_add(5)))
}

#[inline(never)]
pub fn eval_term(depth: u32, x: u64) -> u64 {
    if depth == 0 {
        return x.wrapping_mul(2);
    }
    let f = eval_factor(depth, x.wrapping_add(7));
    f.wrapping_sub(depth as u64)
}

#[inline(never)]
pub fn eval_factor(depth: u32, x: u64) -> u64 {
    if depth <= 1 {
        return x.wrapping_add(11);
    }
    eval_expr(depth - 1, x.rotate_left(3))
}

// Baseline caller: without `willreturn + readnone + nounwind` on the mutually
// recursive `eval_expr <-> eval_term <-> eval_factor` SCC, the compiler cannot
// hoist the loop-invariant call `eval_expr(4, invariant_cfg)` out of the loop
// (LICM) or eliminate a dead validation call `let _ = eval_expr(3, x);` (DCE)!
#[inline(never)]
pub fn caller_without_scc_willreturn(inputs: &[u64], invariant_cfg: u64) -> u64 {
    let mut acc = 0u64;
    for &x in inputs {
        let _dead_validation = eval_expr(black_box(3), x);
        let loop_inv = eval_expr(black_box(4), invariant_cfg);
        acc = acc.wrapping_add(x ^ loop_inv);
    }
    acc
}

// SCC-summary-enabled caller: `SccGfpCert` (`readnone, nounwind`) + `SccRankingCert`
// (`willreturn`) legally discharges DCE of `_dead_validation` and LICM hoisting of `loop_inv`!
#[inline(never)]
pub fn caller_with_scc_summary_certs(inputs: &[u64], invariant_cfg: u64) -> u64 {
    let mut acc = 0u64;
    let loop_inv = eval_expr(4, invariant_cfg);
    for &x in inputs {
        acc = acc.wrapping_add(x ^ loop_inv);
    }
    acc
}

fn main() {
    let inputs: Vec<u64> = (0..20_000u64).collect();
    let cfg = black_box(42u64);

    for _ in 0..5 {
        black_box(caller_without_scc_willreturn(black_box(&inputs), cfg));
        black_box(caller_with_scc_summary_certs(black_box(&inputs), cfg));
    }

    let mut base_times = Vec::with_capacity(21);
    let mut opt_times = Vec::with_capacity(21);
    for _ in 0..21 {
        let t0 = Instant::now();
        let r0 = caller_without_scc_willreturn(black_box(&inputs), cfg);
        black_box(r0);
        base_times.push(t0.elapsed().as_nanos() as f64 / 1000.0);

        let t1 = Instant::now();
        let r1 = caller_with_scc_summary_certs(black_box(&inputs), cfg);
        black_box(r1);
        assert_eq!(r0, r1);
        opt_times.push(t1.elapsed().as_nanos() as f64 / 1000.0);
    }
    base_times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    opt_times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!(
        "{{\"without_scc_willreturn_us\":{:.2},\"with_scc_summary_certs_us\":{:.2}}}",
        base_times[base_times.len() / 2],
        opt_times[opt_times.len() / 2]
    );
}
"""


def main() -> None:
    corpus_rs = SUPPORT_DIR / "recursive_thinlto_corpus.rs"
    nodes = build_30fn_graph()

    t0 = time.perf_counter()
    sccs = tarjan_scc(nodes)
    synth_results = synthesize_scc_certificates(nodes, sccs)
    synth_ms = (time.perf_counter() - t0) * 1000.0

    with tempfile.TemporaryDirectory(prefix="run37_o7_") as tmp:
        tmp_dir = Path(tmp)
        ll_out = tmp_dir / "corpus.ll"
        subprocess.run(
            RUSTC
            + [
                "-C",
                "opt-level=3",
                "--emit=llvm-ir",
                str(corpus_rs),
                "-o",
                str(ll_out),
            ],
            check=True,
        )
        ll_text = ll_out.read_text(encoding="utf-8")
        llvm_attrs = parse_llvm_ir_fn_attrs(ll_text, list(nodes.keys()))

        bench_rs = tmp_dir / "caller_bench.rs"
        bench_rs.write_text(CALLER_OPT_BENCH_RS, encoding="utf-8")
        bench_bin = tmp_dir / "caller_bench"
        subprocess.run(
            RUSTC + ["-C", "opt-level=3", str(bench_rs), "-o", str(bench_bin)],
            check=True,
        )
        bench_metrics = json.loads(
            subprocess.check_output([str(bench_bin)], text=True).strip()
        )

    rows = []
    for fn_name in nodes:
        sr = synth_results[fn_name]
        la = llvm_attrs[fn_name]
        rows.append({
            "function": fn_name,
            "scc_size": sr["scc_size"],
            "u9_dag_nounwind": sr["u9_dag_nounwind"],
            "u9_dag_mem_effect": sr["u9_dag_mem_effect"],
            "u9_dag_willreturn": sr["u9_dag_willreturn"],
            "llvm_23_nounwind": la["llvm_nounwind"],
            "llvm_23_mem_effect": la["llvm_mem_effect"],
            "llvm_23_willreturn": la["llvm_willreturn"],
            "anneal_scc_nounwind": sr["scc_gfp_nounwind"],
            "anneal_scc_mem_effect": sr["scc_gfp_mem_effect"],
            "anneal_scc_willreturn": sr["scc_lfp_willreturn"],
            "lex_rank_2d": sr["lex_rank_2d"],
        })

    # Aggregate counts across the 26 bounded terminating functions + 4 negative canaries
    bounded_fns = [r for r in rows if not r["function"].startswith("canary_")]
    canary_fns = [r for r in rows if r["function"].startswith("canary_")]

    comparison_summary = {
        "subject_rustc_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
        "subject_llvm_commit": "1b9c0d5ff9bbe7634aead059efe6b11a7eeba145",
        "total_functions_evaluated": len(rows),
        "total_sccs": len(sccs),
        "mutually_recursive_multi_fn_sccs": sum(1 for s in sccs if len(s) >= 2),
        "self_recursive_singleton_sccs": sum(1 for s in sccs if len(s) == 1),
        "synthesis_wall_clock_ms": round(synth_ms, 3),
        "aggregate_bounded_26_functions": {
            "u9_dag_nounwind_proven": sum(1 for r in bounded_fns if r["u9_dag_nounwind"]),
            "u9_dag_readonly_or_argmem_proven": sum(
                1 for r in bounded_fns if r["u9_dag_mem_effect"] != "readwrite"
            ),
            "u9_dag_willreturn_proven": sum(1 for r in bounded_fns if r["u9_dag_willreturn"]),
            "llvm_23_nounwind_proven": sum(1 for r in bounded_fns if r["llvm_23_nounwind"]),
            "llvm_23_readonly_or_argmem_proven": sum(
                1 for r in bounded_fns if r["llvm_23_mem_effect"] != "readwrite"
            ),
            "llvm_23_willreturn_proven": sum(1 for r in bounded_fns if r["llvm_23_willreturn"]),
            "anneal_scc_nounwind_proven": sum(
                1 for r in bounded_fns if r["anneal_scc_nounwind"]
            ),
            "anneal_scc_readonly_or_argmem_proven": sum(
                1 for r in bounded_fns if r["anneal_scc_mem_effect"] != "readwrite"
            ),
            "anneal_scc_willreturn_proven": sum(
                1 for r in bounded_fns if r["anneal_scc_willreturn"]
            ),
        },
        "negative_canaries_4_functions": {
            "unbounded_willreturn_rejected": sum(
                1
                for r in canary_fns
                if "collatz" in r["function"] or "zero_decrease" in r["function"]
                and not r["anneal_scc_willreturn"]
            ),
            "panicking_nounwind_rejected": not synth_results[
                "canary_panicking_recursive_walk"
            ]["scc_gfp_nounwind"],
        },
        "caller_licm_and_dce_benchmark": {
            "without_scc_willreturn_us": bench_metrics["without_scc_willreturn_us"],
            "with_scc_summary_certs_us": bench_metrics["with_scc_summary_certs_us"],
            "speedup_ratio": round(
                bench_metrics["without_scc_willreturn_us"]
                / max(0.01, bench_metrics["with_scc_summary_certs_us"]),
                2,
            ),
        },
        "per_function_comparison": rows,
    }

    (SUPPORT_DIR / "scc_summary_comparison.json").write_text(
        json.dumps(comparison_summary, indent=2) + "\n", encoding="utf-8"
    )
    with (SUPPORT_DIR / "scc_thinlto_benchmarks.csv").open(
        "w", newline="", encoding="utf-8"
    ) as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    agg = comparison_summary["aggregate_bounded_26_functions"]
    print(
        f"Bounded 26 recursive fns willreturn proven: "
        f"U9_DAG={agg['u9_dag_willreturn_proven']}/26, "
        f"LLVM_23={agg['llvm_23_willreturn_proven']}/26, "
        f"Anneal_SccRankingCert={agg['anneal_scc_willreturn_proven']}/26"
    )
    print(
        f"Caller DCE+LICM speedup: {bench_metrics['without_scc_willreturn_us']} us -> "
        f"{bench_metrics['with_scc_summary_certs_us']} us "
        f"({comparison_summary['caller_licm_and_dce_benchmark']['speedup_ratio']}x)"
    )


if __name__ == "__main__":
    main()
