#!/usr/bin/env python3
"""Deterministic stdlib verification probe suite for early overlap/conflict
detection signals and dependency-addressed cross-agent shared findings ledgers.

Covers five falsifiable verification modules:

  - Probe 1 (probe_stc_and_palantir_impact):
      Exact Cataldo & Herbsleb (2013) C_R = T_A * T_D * T_A^T and off-diagonal
      STC(C_R, C_A) over non-negative integer coordination counts C_A binarized
      via C_A[i,j] > 0, plus Sarma et al. (2012) Palantir line-ordered diff
      Severity(f) (via difflib.SequenceMatcher opcodes), directory weighted
      severity, and indirect signature Impact. Demonstrates on a controlled
      structural counterexample why syntactic import graphs (CGRAPH) miss
      cross-language/schema/config logical co-change (FCT) breakages while
      FCT-augmented STC catches all 6 seeded breakages without flagging
      uncoupled files.
  - Probe 2 (probe_intrude_exact_features_and_dup_pr):
      Exact reproduction of luyaor/INTRUDE@87a69cbb comp.py / git.py / wordext.py
      9-scalar feature vector (get_delta_code_tokens_counter, get_pull_on_overlap,
      cross hunk-interval overlap, and literal check_pattern including upstream
      comp.py:224's int-vs-str ab_num bug) alongside Sun et al. (2011) multi-field
      text-only BM25F_ext (unigram avg_u + bigram avg_b), evaluated with both an
      explicit [linear feature-ablation discriminator] and an out-of-sample
      decision-stump AdaBoost classifier trained on a disjoint synthetic split.
  - Probe 3 (probe_crystal_speculative_merge_and_stc_gate):
      (3A) Real git execution (requiring Git >= 2.38 for `git merge-tree
      --write-tree`) inside tempfile.TemporaryDirectory() reproducing Crystal's
      (brunyuriy/crystalvc@2275e698) 7-state lattice (SAME, AHEAD, BEHIND,
      TEXTUAL_CONFLICT, BUILD_CONFLICT, TEST_CONFLICT, MERGE_CLEAN) and confirming
      Crystal's Git stdout-substring failure on modern Git (`ort`);
      (3B) N in {8, 16, 32, 64} ring-coupled module scaling simulation reporting
      exact committed-pair conflict rates at N=64 (95.79% clean, 1.84% textual,
      0.66% build, 1.72% test) and separating committed-pair Tier-0 STC compute
      reduction (89.18%, 11,280 -> 1,221) from combined uncommitted+STC compute
      reduction (93.94%, 20,160 -> 1,221).
  - Probe 4 (probe_cdcl_lbd_nogood_sharing):
      Genuine 2-watched-literal 1-UIP CDCL SAT solver across 4 diversified
      portfolio workers measuring learned clauses, exact LBD(C) (Audemard &
      Simon 2009), and BCP literal-scan overhead under No-Share, Share-All,
      AIMD-Size-Only (Hamadi et al. 2009 aimdT: b=8 increase, a=0.125 decrease),
      and Glue-AIMD (LBD <= 2 + |C| <= e_lim), plus a wide-glue fanout AIMD
      sub-check where |C| > e_lim actively throttles LBD=2 clauses alongside
      false-UNSAT corruption from 1 unverified peer nogood vs. witness gating.
  - Probe 5 (probe_gptcache_vcache_vs_merkle_ledger):
      Exact reproduction of zilliztech/GPTCache@a74ac654 adapter.py rank_threshold,
      vcache-project/vCache@50694eeb verified.py logistic MLE + delta-method var_t +
      50-point epsilon_grid tau(s) + len(obs) < 6 cold-start gate + post-explore
      __perform_cache_update (verified.py:418-433 appending (1.0, 0) and inserting
      a duplicate vector via cache.add without evicting the stale H0 entry in B1,
      vs. 100.0% permanent silent stale hits in B2 where tau(1.0) < 0), and
      OpenBMB/ChatDev@464a681b BlackboardMemory recency FIFO vs. the 2-Stage Hybrid
      (scope_key, dep_cone_merkle_sha256, verifier_status) Shared Findings Ledger
      across Mode A (flag aliasing) and Mode B (blob edit H0 -> H1 and file deletion).

Public-only. Python 3.10+ standard library only. Zero persistent disk writes.
"""

from __future__ import annotations

import ast
import copy
import difflib
import hashlib
import json
import math
import os
import py_compile
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from statistics import NormalDist

SEED = 20261122
STANDARD_NORMAL = NormalDist(0.0, 1.0)


# =============================================================================
# PROBE 1: Cataldo & Herbsleb (2013) STC + Palantir (Sarma et al. 2012) Impact
# =============================================================================


def matmul_int(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    rows, inner, cols = len(a), len(b), len(b[0])
    assert all(len(r) == inner for r in a)
    return [
        [sum(a[i][k] * b[k][j] for k in range(inner)) for j in range(cols)]
        for i in range(rows)
    ]


def transpose_int(m: list[list[int]]) -> list[list[int]]:
    return [[m[r][c] for r in range(len(m))] for c in range(len(m[0]))]


def compute_stc(c_r: list[list[int]], c_a: list[list[int]]) -> tuple[float, int, int]:
    """Exact Cataldo & Herbsleb (2013, Section 5, pp. 347-348) off-diagonal STC.

    Both C_R and C_A belong to N_0^{W x W} (interaction counts in C_A are
    binarized via C_A[i][j] > 0 when testing congruence satisfaction).
    """
    n = len(c_r)
    req_cells = 0
    sat_cells = 0
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            if c_r[i][j] > 0:
                req_cells += 1
                if c_a[i][j] > 0:
                    sat_cells += 1
    stc = (sat_cells / req_cells) if req_cells > 0 else 1.0
    return stc, sat_cells, req_cells


def non_comment_lines(src: str) -> list[str]:
    out = []
    for raw in src.splitlines():
        s = raw.strip()
        if not s or s.startswith("//") or s.startswith("#"):
            continue
        out.append(s)
    return out


def palantir_file_severity(base_src: str, ws_src: str) -> tuple[float, int, int]:
    """Line-ordered diff severity per Sarma et al. (2012, Section 5.5, p. 894)."""
    base_nc = non_comment_lines(base_src)
    ws_nc = non_comment_lines(ws_src)
    matcher = difflib.SequenceMatcher(None, base_nc, ws_nc, autojunk=False)
    changed = sum(
        max(i2 - i1, j2 - j1)
        for tag, i1, i2, j1, j2 in matcher.get_opcodes()
        if tag != "equal"
    )
    denom = max(1, len(base_nc))
    return changed / denom, changed, denom


def extract_pub_signatures(src: str) -> dict[str, int]:
    """Extract public function name -> parameter count for Rust (`pub fn`) or Python (`def`)."""
    sigs: dict[str, int] = {}
    for line in non_comment_lines(src):
        m_rs = re.match(r"pub\s+fn\s+([A-Za-z_]\w*)\s*\(([^)]*)\)", line)
        if m_rs:
            params = [p.strip() for p in m_rs.group(2).split(",") if p.strip()]
            sigs[m_rs.group(1)] = len(params)
            continue
        m_py = re.match(r"def\s+([A-Za-z_]\w*)\s*\(([^)]*)\)", line)
        if m_py and not m_py.group(1).startswith("_"):
            params = [p.strip() for p in m_py.group(2).split(",") if p.strip()]
            sigs[m_py.group(1)] = len(params)
    return sigs


def extract_symbol_calls(src: str) -> dict[str, set[int]]:
    calls: dict[str, set[int]] = {}
    for line in non_comment_lines(src):
        if line.startswith("pub fn ") or line.startswith("def "):
            continue
        for m in re.finditer(r"\b([A-Za-z_]\w*)\s*\(([^()]*)\)", line):
            fn = m.group(1)
            if fn in {"if", "for", "while", "return", "assert"}:
                continue
            args = [a.strip() for a in m.group(2).split(",") if a.strip()]
            calls.setdefault(fn, set()).add(len(args))
    return calls


def probe_stc_and_palantir_impact() -> dict[str, object]:
    banner = (
        "[exact reproduction of pinned repository logic] + "
        "[controlled combinatorial / simulation experiment]"
    )
    files = [
        "src/wire.rs",          # 0: Rust wire header serializer
        "src/codec.rs",         # 1: Rust codec calling wire.rs
        "src/router.rs",        # 2: Rust route dispatcher
        "src/metrics.rs",       # 3: Independent Rust telemetry counter
        "py/schema.py",         # 4: Python wire struct decoder (coupled to wire.rs + frame.proto)
        "py/client.py",         # 5: Python SDK calling py/schema.py
        "py/tests_e2e.py",      # 6: Independent Python unit test helper
        "proto/frame.proto",    # 7: Wire protobuf schema (coupled to wire.rs + py/schema.py)
        "sql/004_ledger.sql",   # 8: Ledger migration (coupled to codec.rs)
        "config/flags.toml",    # 9: Feature flag defaults (coupled to router.rs + ci/matrix.yaml)
        "ci/matrix.yaml",       # 10: CI feature matrix
        "benches/bench.rs",     # 11: Benchmark calling codec.rs
    ]
    n_files = len(files)
    f_idx = {name: i for i, name in enumerate(files)}

    # Controlled structural counterexample: syntactic intra-language call/import graph (CGRAPH)
    # has zero edges across Rust/Python/Proto/SQL/TOML boundaries.
    cgraph_edges = [
        ("src/wire.rs", "src/codec.rs"),
        ("src/codec.rs", "src/router.rs"),
        ("src/codec.rs", "benches/bench.rs"),
        ("py/schema.py", "py/client.py"),
    ]
    td_cgraph = [[0] * n_files for _ in range(n_files)]
    for u, v in cgraph_edges:
        iu, iv = f_idx[u], f_idx[v]
        td_cgraph[iu][iv] = 1
        td_cgraph[iv][iu] = 1

    # Historical Modification Requests (24 prior MRs) inducing FCT ("Files Changed Together")
    historical_mrs: list[tuple[str, ...]] = (
        [("src/wire.rs", "src/codec.rs")] * 4
        + [("src/codec.rs", "src/router.rs")] * 3
        + [("py/schema.py", "py/client.py")] * 4
        + [("src/wire.rs", "proto/frame.proto", "py/schema.py")] * 5
        + [("src/codec.rs", "sql/004_ledger.sql")] * 3
        + [("src/router.rs", "config/flags.toml", "ci/matrix.yaml")] * 4
        + [("src/codec.rs", "benches/bench.rs")] * 1
    )
    assert len(historical_mrs) == 24
    td_fct = [[0] * n_files for _ in range(n_files)]
    for mr in historical_mrs:
        for i in range(len(mr)):
            for j in range(i + 1, len(mr)):
                a, b = f_idx[mr[i]], f_idx[mr[j]]
                td_fct[a][b] += 1
                td_fct[b][a] += 1

    # W = 6 agents partitioned into 3 language-aligned 2-agent teams:
    # Team Rust: W0, W1 | Team Python: W2, W3 | Team Schema/Config: W4, W5
    n_workers = 6
    worker_files = {
        0: ["src/wire.rs"],
        1: ["src/codec.rs", "src/router.rs"],
        2: ["py/schema.py", "py/client.py"],
        3: ["py/tests_e2e.py"],
        4: ["proto/frame.proto", "sql/004_ledger.sql"],
        5: ["config/flags.toml", "src/metrics.rs"],
    }
    t_a = [[0] * n_files for _ in range(n_workers)]
    for w, flist in worker_files.items():
        for fname in flist:
            t_a[w][f_idx[fname]] = 1

    # Block-diagonal team coordination count matrix C_A in N_0^{W x W}
    # (Cataldo & Herbsleb 2013, p. 348: interaction counts binarized via C_A[i,j] > 0)
    c_a_siloed = [[0] * n_workers for _ in range(n_workers)]
    for a, b, msg_cnt in [(0, 1, 4), (2, 3, 2), (4, 5, 3)]:
        c_a_siloed[a][b] = msg_cnt
        c_a_siloed[b][a] = msg_cnt

    # Exact C_R = T_A * T_D * T_A^T (workers x files) * (files x files) * (files x workers)
    t_a_t = transpose_int(t_a)
    cr_cgraph = matmul_int(matmul_int(t_a, td_cgraph), t_a_t)
    cr_fct = matmul_int(matmul_int(t_a, td_fct), t_a_t)
    assert len(cr_fct) == n_workers and len(cr_fct[0]) == n_workers

    for i in range(n_workers):
        for j in range(n_workers):
            assert cr_fct[i][j] == cr_fct[j][i]
            expected = sum(
                t_a[i][f1] * td_fct[f1][f2] * t_a[j][f2]
                for f1 in range(n_files)
                for f2 in range(n_files)
            )
            assert cr_fct[i][j] == expected

    stc_cgraph, sat_cg, req_cg = compute_stc(cr_cgraph, c_a_siloed)
    stc_fct_siloed, sat_fct, req_fct = compute_stc(cr_fct, c_a_siloed)

    # Non-vacuity negative control: W3 (py/tests_e2e.py) has ZERO required coordination with all 5 peers
    assert all(cr_fct[3][j] == 0 for j in range(n_workers) if j != 3)

    # Palantir line-ordered diff Severity(f), directory compound severity, and indirect signature Impact
    base_wire = (
        "// Wire header v1\n"
        "pub fn encode_header(magic: u32, payload_len: u32) -> u64 {\n"
        "    ((magic as u64) << 32) | (payload_len as u64)\n"
        "}\n"
        "pub fn header_size() -> usize {\n"
        "    8\n"
        "}\n"
    )
    w0_wire_sig_change = (
        "// Wire header v2 with flags\n"
        "pub fn encode_header(magic: u32, flags: u8, payload_len: u32) -> u64 {\n"
        "    ((magic as u64) << 40) | ((flags as u64) << 32) | (payload_len as u64)\n"
        "}\n"
        "pub fn header_size() -> usize {\n"
        "    8\n"
        "}\n"
    )
    w0_wire_body_only = (
        "// Wire header v1body\n"
        "pub fn encode_header(magic: u32, payload_len: u32) -> u64 {\n"
        "    ((magic as u64) << 32) ^ (payload_len as u64)\n"
        "}\n"
        "pub fn header_size() -> usize {\n"
        "    8\n"
        "}\n"
    )
    # Reordering functions with identical line multiset must register non-zero line-diff severity
    w0_wire_reordered = (
        "// Reordered functions\n"
        "pub fn header_size() -> usize {\n"
        "    8\n"
        "}\n"
        "pub fn encode_header(magic: u32, payload_len: u32) -> u64 {\n"
        "    ((magic as u64) << 32) | (payload_len as u64)\n"
        "}\n"
    )
    w1_codec_caller = (
        "pub fn build_packet(n: u32) -> u64 {\n"
        "    encode_header(0xCAFE, n)\n"
        "}\n"
    )

    sev_sig, chg_sig, loc_sig = palantir_file_severity(base_wire, w0_wire_sig_change)
    sev_body, _, _ = palantir_file_severity(base_wire, w0_wire_body_only)
    sev_reord, chg_reord, _ = palantir_file_severity(base_wire, w0_wire_reordered)
    assert abs(sev_sig - (2.0 / 6.0)) < 1e-9 and chg_sig == 2 and loc_sig == 6
    assert abs(sev_body - (1.0 / 6.0)) < 1e-9
    assert sev_reord > 0.0 and chg_reord == 6

    dir_weighted_sev = (2 + 1) / (6 + 3)
    assert abs(dir_weighted_sev - (1.0 / 3.0)) < 1e-9

    def palantir_indirect_impact(base_f: str, mod_f: str, peer_f: str, cgraph_coupled: bool) -> bool:
        if not cgraph_coupled:
            return False
        s_base = extract_pub_signatures(base_f)
        s_mod = extract_pub_signatures(mod_f)
        peer_calls = extract_symbol_calls(peer_f)
        for sym, arities in peer_calls.items():
            if sym in s_base and (sym not in s_mod or s_mod[sym] not in arities):
                return True
        return False

    impact_on_sig_change = palantir_indirect_impact(base_wire, w0_wire_sig_change, w1_codec_caller, True)
    impact_on_body_only = palantir_indirect_impact(base_wire, w0_wire_body_only, w1_codec_caller, True)
    assert impact_on_sig_change is True
    assert impact_on_body_only is False

    seeded_breakages = [
        ("W0->W1_rust_sig", 0, 1, "intra_lang_sig"),
        ("W1->W0_rust_router_codec", 1, 0, "intra_lang_sig"),
        ("W0<->W2_rust_py_wire_schema", 0, 2, "cross_lang_schema"),
        ("W0<->W4_rust_proto_frame", 0, 4, "cross_lang_schema"),
        ("W1<->W4_codec_sql_migration", 1, 4, "cross_lang_schema"),
        ("W1<->W5_router_toml_flags", 1, 5, "cross_lang_config"),
    ]
    cgraph_caught = sum(1 for _, u, v, _ in seeded_breakages if cr_cgraph[u][v] > 0)
    cgraph_cross_caught = sum(
        1 for _, u, v, kind in seeded_breakages if kind != "intra_lang_sig" and cr_cgraph[u][v] > 0
    )
    fct_caught = sum(1 for _, u, v, _ in seeded_breakages if cr_fct[u][v] > 0)

    c_a_repaired = [row[:] for row in c_a_siloed]
    added_links = 0
    for i in range(n_workers):
        for j in range(i + 1, n_workers):
            if cr_fct[i][j] > 0 and c_a_repaired[i][j] == 0:
                c_a_repaired[i][j] = 1
                c_a_repaired[j][i] = 1
                added_links += 1
    stc_fct_repaired, _, _ = compute_stc(cr_fct, c_a_repaired)

    assert abs(stc_cgraph - 1.0) < 1e-9
    assert cgraph_cross_caught == 0 and cgraph_caught == 2
    assert fct_caught == len(seeded_breakages) == 6
    assert stc_fct_siloed < 0.25 and abs(1.0 - stc_fct_siloed - (10.0 / 12.0)) < 1e-9
    assert abs(stc_fct_repaired - 1.0) < 1e-9 and added_links == 5

    return {
        "banner": banner,
        "matrix_dimensions": {"T_A": [n_workers, n_files], "T_D": [n_files, n_files], "C_R": [n_workers, n_workers]},
        "c_a_domain": "N_0^{W x W} binarized via C_A[i,j] > 0 (Cataldo & Herbsleb 2013, p. 348)",
        "stc_under_cgraph_siloed": round(stc_cgraph, 4),
        "stc_under_fct_siloed": round(stc_fct_siloed, 4),
        "coordination_breakdown_gap_fct": round(1.0 - stc_fct_siloed, 4),
        "stc_under_fct_after_targeted_sync": round(stc_fct_repaired, 4),
        "required_offdiag_pairs_cgraph_vs_fct": [req_cg, req_fct],
        "targeted_cross_team_links_added": added_links,
        "uncoupled_worker_w3_false_links": sum(cr_fct[3][j] > 0 for j in range(n_workers) if j != 3),
        "palantir_wire_severity_opcodes": round(sev_sig, 4),
        "palantir_reordered_lines_severity_opcodes": round(sev_reord, 4),
        "palantir_impact_sig_vs_body_control": [impact_on_sig_change, impact_on_body_only],
        "seeded_breakage_recall_structural_counterexample": {
            "cgraph_overall": f"{cgraph_caught}/{len(seeded_breakages)}",
            "cgraph_cross_layer": f"{cgraph_cross_caught}/4",
            "fct_overall": f"{fct_caught}/{len(seeded_breakages)}",
        },
    }


# =============================================================================
# PROBE 2: INTRUDE (luyaor/INTRUDE@87a69cbb) Exact 9 Features + BM25F_ext
# =============================================================================

GENERAL_STOPWORDS = frozenset(
    {
        "the", "and", "for", "with", "when", "from", "that", "this", "into",
        "are", "was", "were", "has", "have", "had", "not", "but", "all", "can",
        "in", "on", "to", "of", "by", "at", "or", "is", "if", "it", "as", "be", "an",
    }
)


def intrude_camel_case_split(identifier: str) -> list[str]:
    """Exact luyaor/INTRUDE@87a69cbb util/wordext.py:15-17."""
    matches = re.finditer(r".+?(?:(?<=[a-z])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])|$)", identifier)
    return [m.group(0) for m in matches]


def intrude_word_split_by_char(token: str) -> list[str]:
    """Exact luyaor/INTRUDE@87a69cbb util/wordext.py:19-50."""
    old_words = [token]
    result: list[str] = []
    while old_words:
        new_words: list[str] = []
        for s in old_words:
            if "-" in s:
                new_words += s.split("-")
            elif "." in s:
                new_words += s.split(".")
            elif "_" in s:
                new_words += s.split("_")
            elif "/" in s:
                new_words += s.split("/")
            elif "\\" in s:
                new_words += s.split("\\")
            else:
                t = intrude_camel_case_split(s)
                if len(t) > 1:
                    new_words += t
                result.append(s)
        old_words = new_words
    return result


def light_stem(w: str) -> str:
    for suf in ("ing", "ed", "es", "s"):
        if len(w) > len(suf) + 3 and w.endswith(suf):
            return w[: -len(suf)]
    return w


def intrude_tokenize(text: str) -> list[str]:
    raw_tokens = re.findall(r"[A-Za-z0-9_./-]+", text or "")
    split_tokens: list[str] = []
    for tok in raw_tokens:
        split_tokens.extend(intrude_word_split_by_char(tok))
    out: list[str] = []
    for tok in split_tokens:
        if not re.search(r"[0-9A-Za-z_]", tok):
            continue
        low = tok.lower()
        if low in GENERAL_STOPWORDS or len(low) < 2:
            continue
        out.append(light_stem(low))
    return out


def intrude_counter_similarity(a_c: Counter[str], b_c: Counter[str]) -> float:
    """Exact comp.py:30-38 multiset Jaccard."""
    union = sorted(set(a_c) | set(b_c))
    tot1 = sum(min(a_c.get(x, 0), b_c.get(x, 0)) for x in union)
    tot2 = sum(max(a_c.get(x, 0), b_c.get(x, 0)) for x in union)
    return (tot1 / tot2) if tot2 > 0 else 0.0


def intrude_get_delta_code_tokens_counter(add_tokens: list[str], del_tokens: list[str]) -> Counter[str]:
    """Exact comp.py:87-99 net-added token counter."""
    add_c = Counter(add_tokens)
    del_c = Counter(del_tokens)
    changed_c: Counter[str] = Counter()
    for t in sorted(add_c):
        times = add_c[t] - del_c[t]
        if times > 0:
            changed_c[t] = times
    return changed_c


def intrude_get_pull_on_overlap(pull: dict[str, object], overlap_set: set[str]) -> dict[str, object]:
    """Exact comp.py:82-85 restriction to overlapping changed files."""
    new_pull = copy.deepcopy(pull)
    flist = new_pull["file_list"]
    assert isinstance(flist, list)
    new_pull["file_list"] = [x for x in flist if x["name"] in overlap_set]
    return new_pull


def intrude_get_location(pull: dict[str, object]) -> list[list[object]]:
    """Exact comp.py:67-72 added-hunk intervals [file_name, start, start + count]."""
    loc_set: list[list[object]] = []
    flist = pull["file_list"]
    assert isinstance(flist, list)
    for f in flist:
        for start, count in f["location"]["add"]:
            loc_set.append([f["name"], int(start), int(start) + int(count)])
    return loc_set


def intrude_location_similarity(la: list[list[object]], lb: list[list[object]]) -> float:
    """Exact comp.py:103-159 line-weighted hunk-interval cross similarity."""

    def cross(x1: int, y1: int, x2: int, y2: int) -> bool:
        return not ((y1 < x2) or (y2 < x1))

    if len(la) + len(lb) == 0:
        return 0.0
    match_a = [False] * len(la)
    match_b = [False] * len(lb)
    index_b: dict[str, list[int]] = {}
    for idx, item in enumerate(lb):
        fname = str(item[0])
        index_b.setdefault(fname, []).append(idx)
    for i, item_a in enumerate(la):
        fname = str(item_a[0])
        x1, y1 = int(item_a[1]), int(item_a[2])
        for j in index_b.get(fname, []):
            x2, y2 = int(lb[j][1]), int(lb[j][2])
            if cross(x1, y1, x2, y2):
                match_a[i] = True
                match_b[j] = True
    a_match = sum((int(la[i][2]) - int(la[i][1])) for i in range(len(la)) if match_a[i])
    a_tot = sum((int(la[i][2]) - int(la[i][1])) for i in range(len(la)))
    b_match = sum((int(lb[j][2]) - int(lb[j][1])) for j in range(len(lb)) if match_b[j])
    b_tot = sum((int(lb[j][2]) - int(lb[j][1])) for j in range(len(lb)))
    return ((a_match + b_match) / (a_tot + b_tot)) if (a_tot + b_tot) > 0 else 0.0


def intrude_check_pattern_pinned(a: dict[str, object], b: dict[str, object]) -> int:
    """Verbatim reproduction of luyaor/INTRUDE@87a69cbb comp.py:223-240 + git.py:38-57.

    Preserves upstream comp.py:224's literal `ab_num = set([a["number"], b["number"]])`
    where GitHub JSON `number` is an `int` subtracted from `str` regex matches!
    """

    def get_numbers(text: str) -> list[str]:
        return sorted({x for x in re.findall(r"([0-9]+)", text) if len(x) >= 3})

    def get_version_numbers(text: str) -> list[str]:
        return sorted({"".join(x) for x in re.findall(r"(\d+\.)?(\d+\.)(\d+)", text)})

    def get_pr_and_issue_numbers(text: str) -> list[str]:
        nums = (
            re.findall(r"#([0-9]+)", text)
            + re.findall(r"pull/([0-9]+)", text)
            + re.findall(r"issues/([0-9]+)", text)
        )
        return sorted({x for x in nums if len(x) > 0})

    # Literal upstream comp.py:224 (`int` elements fail to subtract from `str` sets)
    ab_num = {a["number"], b["number"]}
    a_text = f"{a['title']} {a['body']}"
    b_text = f"{b['title']} {b['body']}"

    a_set = set(get_numbers(a_text) + get_version_numbers(a_text)) - ab_num  # type: ignore[operator]
    b_set = set(get_numbers(b_text) + get_version_numbers(b_text)) - ab_num  # type: ignore[operator]
    if a_set & b_set:
        return 1
    a_res = set(get_pr_and_issue_numbers(a_text) + get_version_numbers(a_text)) - ab_num  # type: ignore[operator]
    b_res = set(get_pr_and_issue_numbers(b_text) + get_version_numbers(b_text)) - ab_num  # type: ignore[operator]
    if a_res and b_res and (a_res != b_res):
        return -1
    return 0


def check_pattern_hardened(a: dict[str, object], b: dict[str, object]) -> int:
    """Hardened issue-reference discriminator fixing INTRUDE's 2-digit, bare-number, and int-vs-str bugs."""

    def extract_explicit_refs(text: str) -> set[str]:
        refs = (
            re.findall(r"#([0-9]+)", text)
            + re.findall(r"pull/([0-9]+)", text)
            + re.findall(r"issues/([0-9]+)", text)
        )
        return set(refs)

    ab_num = {str(a["number"]), str(b["number"])}
    ia = extract_explicit_refs(f"{a['title']} {a['body']}") - ab_num
    ib = extract_explicit_refs(f"{b['title']} {b['body']}") - ab_num
    if ia & ib:
        return 1
    if ia and ib:
        return -1
    return 0


class TfIdfCorpus:
    def __init__(self, docs: list[list[str]]) -> None:
        self.n_docs = max(1, len(docs))
        df: Counter[str] = Counter()
        for d in docs:
            for tok in set(d):
                df[tok] += 1
        self.idf = {tok: math.log((self.n_docs + 1.0) / (cnt + 1.0)) + 1.0 for tok, cnt in df.items()}

    def cosine(self, a: Counter[str], b: Counter[str]) -> float:
        if not a or not b:
            return 0.0
        va = {k: v * self.idf.get(k, 1.0) for k, v in a.items()}
        vb = {k: v * self.idf.get(k, 1.0) for k, v in b.items()}
        dot = sum(va[k] * vb[k] for k in sorted(va.keys() & vb.keys()))
        na = math.sqrt(sum(x * x for x in va.values()))
        nb = math.sqrt(sum(x * x for x in vb.values()))
        return (dot / (na * nb)) if (na > 0 and nb > 0) else 0.0


def bm25f_ext_score(
    doc: dict[str, object],
    query: dict[str, object],
    idf_map: dict[str, float],
    avg_lens: tuple[float, float],
    ngram_n: int,
) -> float:
    """Text-only multi-field BM25F_ext (Sun et al., ASE 2011, Eq. 1-5; unigrams + bigrams)."""

    def ngrams(toks: list[str]) -> list[str]:
        if ngram_n == 1:
            return toks
        return [f"{toks[i]}_{toks[i + 1]}" for i in range(len(toks) - 1)]

    d_sum = ngrams(intrude_tokenize(str(doc["title"])))
    d_desc = ngrams(intrude_tokenize(str(doc["body"]))[:400])
    q_sum = ngrams(intrude_tokenize(str(query["title"])))
    q_desc = ngrams(intrude_tokenize(str(query["body"]))[:400])

    c_ds, c_dd = Counter(d_sum), Counter(d_desc)
    c_qs, c_qd = Counter(q_sum), Counter(q_desc)
    w_s, w_d = 3.0, 1.0
    b_s, b_d = 0.5, 0.8
    k1, k3 = 2.0, 1.2
    avg_s, avg_d = max(1.0, avg_lens[0]), max(1.0, avg_lens[1])

    shared = sorted((set(c_ds) | set(c_dd)) & (set(c_qs) | set(c_qd)))
    score = 0.0
    for term in shared:
        tf_d = 0.0
        if c_ds[term] > 0:
            tf_d += w_s * c_ds[term] / (1.0 - b_s + b_s * (len(d_sum) / avg_s))
        if c_dd[term] > 0:
            tf_d += w_d * c_dd[term] / (1.0 - b_d + b_d * (len(d_desc) / avg_d))
        tf_q = w_s * c_qs[term] + w_d * c_qd[term]
        score += idf_map.get(term, 1.0) * (tf_d / (k1 + tf_d)) * (((k3 + 1.0) * tf_q) / (k3 + tf_q))
    return score


@dataclass(frozen=True)
class DecisionStump:
    feat_idx: int
    threshold: float
    left_score: float
    right_score: float

    def score(self, x: list[float]) -> float:
        return self.right_score if x[self.feat_idx] >= self.threshold else self.left_score


def train_decision_stump_adaboost(
    xs: list[list[float]],
    ys: list[int],
    n_estimators: int = 20,
    learning_rate: float = 0.5,
) -> list[DecisionStump]:
    """Deterministic stdlib Real AdaBoost / SAMME.R over 1D decision stumps
    (Friedman, Hastie, & Tibshirani 2000; default algorithm in sklearn's
    AdaBoostClassifier used by INTRUDE clf.py:269).
    """
    n = len(xs)
    n_dim = len(xs[0])
    weights = [1.0 / n] * n
    stumps: list[DecisionStump] = []
    eps = 1e-6

    candidate_thresholds: list[list[float]] = []
    for d in range(n_dim):
        vals = sorted({round(row[d], 6) for row in xs})
        mids = [(vals[k] + vals[k + 1]) * 0.5 for k in range(len(vals) - 1)]
        candidate_thresholds.append([vals[0] - 0.01] + vals + mids + [vals[-1] + 0.01])

    for _ in range(n_estimators):
        best_z = float("inf")
        best_stump = DecisionStump(0, 0.0, 0.0, 0.0)
        for d in range(n_dim):
            for thr in candidate_thresholds[d]:
                wp_l = wn_l = wp_r = wn_r = 0.0
                for i in range(n):
                    if xs[i][d] >= thr:
                        if ys[i] == 1:
                            wp_r += weights[i]
                        else:
                            wn_r += weights[i]
                    else:
                        if ys[i] == 1:
                            wp_l += weights[i]
                        else:
                            wn_l += weights[i]
                # Exact Real AdaBoost partition criterion: minimize Z = 2*(sqrt(wp_l*wn_l) + sqrt(wp_r*wn_r))
                z_crit = 2.0 * (math.sqrt(wp_l * wn_l) + math.sqrt(wp_r * wn_r))
                if z_crit < best_z - 1e-12:
                    best_z = z_crit
                    f_l = learning_rate * 0.5 * math.log((wp_l + eps) / (wn_l + eps))
                    f_r = learning_rate * 0.5 * math.log((wp_r + eps) / (wn_r + eps))
                    best_stump = DecisionStump(d, thr, f_l, f_r)
        stumps.append(best_stump)
        norm = 0.0
        for i in range(n):
            weights[i] *= math.exp(-ys[i] * best_stump.score(xs[i]))
            norm += weights[i]
        weights = [w / norm for w in weights]
    return stumps


def adaboost_predict(stumps: list[DecisionStump], x: list[float]) -> bool:
    return sum(st.score(x) for st in stumps) >= 0.0


def probe_intrude_exact_features_and_dup_pr() -> dict[str, object]:
    banner = (
        "[exact reproduction of pinned repository logic] + "
        "[controlled combinatorial / simulation experiment]"
    )

    def make_pr(
        num: int,
        title: str,
        body: str,
        comp: str,
        files: list[tuple[str, list[tuple[int, int]], str, str]],
    ) -> dict[str, object]:
        return {
            "number": num,
            "title": title,
            "body": body,
            "component": comp,
            "file_list": [
                {
                    "name": fn,
                    "location": {"add": [[s, c] for s, c in hunks]},
                    "add_code": add_c,
                    "del_code": del_c,
                }
                for fn, hunks, add_c, del_c in files
            ],
        }

    # 1. Verify all 4 pinned INTRUDE check_pattern source bugs directly
    p_42a = make_pr(10, "Fix crash", "Fixes #42 on startup", "core", [])
    p_42b = make_pr(11, "Guard null", "Resolves #42 during init", "core", [])
    p_42_multi = make_pr(12, "Fix crash", "Fixes #42 and #105", "core", [])
    p_http_a = make_pr(13, "Auth route", "Fixes #101 when upstream returns 404", "router", [])
    p_http_b = make_pr(14, "Billing route", "Fixes #204 when webhook returns 404", "router", [])
    p_self_105 = make_pr(105, "Refactor parser", "PR #105 template self-checklist", "core", [])
    p_self_208 = make_pr(208, "Refactor parser", "PR #208 template self-checklist", "core", [])

    pinned_e1 = intrude_check_pattern_pinned(p_42a, p_42b)             # 0 instead of +1 (len("42") < 3)
    pinned_e2 = intrude_check_pattern_pinned(p_42_multi, p_42b)        # -1 instead of +1
    pinned_e3 = intrude_check_pattern_pinned(p_http_a, p_http_b)       # +1 instead of -1 (shared "404")
    pinned_e4 = intrude_check_pattern_pinned(p_self_105, p_self_208)   # -1 instead of 0 (int-vs-str ab_num!)
    hard_e1 = check_pattern_hardened(p_42a, p_42b)
    hard_e2 = check_pattern_hardened(p_42_multi, p_42b)
    hard_e3 = check_pattern_hardened(p_http_a, p_http_b)
    hard_e4 = check_pattern_hardened(p_self_105, p_self_208)
    assert (pinned_e1, pinned_e2, pinned_e3, pinned_e4) == (0, -1, 1, -1)
    assert (hard_e1, hard_e2, hard_e3, hard_e4) == (1, 1, -1, 0)

    # 2. Held-out 20-pair evaluation benchmark:
    cold_specs = [
        ("CLI hangs indefinitely after broken pipe", "User session freezes if stdout consumer exits",
         "Return EOF sentinel on empty chunk read", "Terminate poll loop when read_exact yields zero octets",
         "src/io/framing_reader.py", 42, "if n_read == 0:\n    return FrameEOF\n", "buf.extend(chunk)\n"),
        ("Export CSV silently drops final row", "Spreadsheet download missing trailing record",
         "Flush BufferedWriter before closing sink handle", "Invoke stream.flush_all in CsvSink::finish",
         "src/export/csv_sink.py", 88, "self._writer.flush_pending()\n", "self._handle.close()\n"),
        ("TLS handshake fails behind corporate proxy", "HTTPS connection resets on custom CA bundle",
         "Append system PEM roots to SSLContext store", "Load extra_certs into X509StoreBuilder",
         "src/net/tls_context.py", 61, "ctx.load_verify_locations(cafile=bundle_path)\n", "ctx.set_default_verify()\n"),
        ("Dark mode flickers white during tab switch", "Theme flashes bright background on navigation",
         "Hydrate CSS variables synchronously in head script", "Inline palette_tokens before initial paint",
         "src/ui/theme_boot.py", 19, "inject_sync_palette(doc_head, active_palette)\n", "defer_palette_load()\n"),
        ("Memory usage climbs linearly in idle worker", "Daemon RSS reaches 4GB overnight with zero jobs",
         "Evict expired span trace buffers in heartbeat", "Purge completed_spans ring on timer tick",
         "src/telemetry/span_ring.py", 114, "self._completed_spans.clear_expired(now_ts)\n", "pass\n"),
        ("Pagination repeats items across page boundary", "Duplicate entries shown on scroll",
         "Add deterministic primary-key tiebreaker to ORDER BY", "Append id ASC secondary sort key in cursor query",
         "src/db/cursor_pager.py", 73, "order_clause = f'{sort_col} DESC, record_id ASC'\n", "order_clause = f'{sort_col} DESC'\n"),
        ("Webhook signature validation rejects UTF-8 payload", "Non-ASCII customer names fail HMAC check",
         "Compute SHA256 digest over raw request octets", "Pass undecodedwire_buf into hmac.compare_digest",
         "src/auth/hmac_guard.py", 33, "mac.update(raw_body_bytes)\n", "mac.update(body_text.encode('ascii'))\n"),
        ("Retry backoff stalls all unrelated queues", "Slow tenant throttles healthy background tasks",
         "Replace time.sleep with per-tenant async deadline", "Schedule delayed requeue on min-heap without blocking loop",
         "src/queue/retry_wheel.py", 95, "retry_heap.push(now + delay_s, tenant_job)\n", "time.sleep(delay_s)\n"),
    ]
    paraphrase_specs = [
        ("Fix integer overflow in token bucket refill", "Prevent token bucket refill multiplication overflow",
         "Clamp elapsed nanoseconds before rate multiply in bucket.py", "Guard elapsed_ns * rate_per_sec overflow in token bucket",
         "src/ratelimit/bucket.py", 27, "tokens = min(cap, cur + min(elapsed_ns, MAX_NS) * rate)\n"),
        ("Add timeout parameter to Redis lock acquire", "Support configurable lock acquisition timeout in RedisLock",
         "Pass acquire_timeout_ms to SET NX PX loop in redis_lock.py", "Expose acquire_timeout_ms in RedisLock.acquire",
         "src/locks/redis_lock.py", 52, "deadline = monotonic_ms() + acquire_timeout_ms\n"),
        ("Normalize Windows backslashes in manifest paths", "Convert backslash separators to POSIX in manifest loader",
         "Normalize relative artifact paths with as_posix in manifest.py", "Replace backslash path separators in manifest parser",
         "src/pkg/manifest.py", 64, "norm_path = raw_path.replace('\\\\', '/')\n"),
        ("Skip symlink cycles during workspace directory scan", "Detect recursive symlink loops in workspace walker",
         "Track visited (st_dev, st_ino) pairs in scanner.py", "Record inode keys to break symlink loops in workspace scanner",
         "src/fs/scanner.py", 105, "visited_inodes.add((st.st_dev, st.st_ino))\n"),
        ("Validate cron expression field bounds before scheduling", "Reject out-of-range minute and hour fields in cron parser",
         "Raise CronSyntaxError when minute > 59 or hour > 23", "Check 0<=minute<=59 and 0<=hour<=23 in cron_spec.py",
         "src/sched/cron_spec.py", 41, "if not (0 <= minute <= 59 and 0 <= hour <= 23): raise CronSyntaxError()\n"),
        ("Cache compiled JSON schema validators per draft URI", "Memoize Draft2020Validator instances by schema digest",
         "Store compiled schema validator in LRU dict in validator.py", "Avoid recompiling JSON schema validator on every request",
         "src/validation/validator.py", 16, "validator = _SCHEMA_CACHE.setdefault(schema_sha, compile_schema(raw))\n"),
    ]
    registry_nondup_specs = [
        (301, 402, "Register /v1/invoicesarchive endpoint", "Fixes #301 invoice archive route",
         "Register /v1/webhooksreplay endpoint", "Fixes #402 webhook replay route", 140, 142,
         "REGISTRY.register_route('/v1/invoices/archive', RouteSpec(handler=archive_handler, auth='token'))\n",
         "REGISTRY.register_route('/v1/webhooks/replay', RouteSpec(handler=replay_handler, auth='token'))\n"),
        (303, 404, "Add feature flag enable_vector_quant", "Closes #303 quantization toggle",
         "Add feature flag enable_audit_export", "Closes #404 audit log toggle", 80, 81,
         "FLAGS.define_bool('enable_vector_quant', default=False, owner='search')\n",
         "FLAGS.define_bool('enable_audit_export', default=False, owner='compliance')\n"),
        (305, 406, "Wire CLI subcommand `fleet drain`", "Fixes #305 node drain subcommand",
         "Wire CLI subcommand `fleet cordon`", "Fixes #406 node cordon subcommand", 210, 212,
         "SUBCOMMANDS.register_command('drain', CommandSpec(run=run_drain, admin=True))\n",
         "SUBCOMMANDS.register_command('cordon', CommandSpec(run=run_cordon, admin=True))\n"),
        (307, 408, "Register error code E4102_QUOTA_EXCEEDED", "Resolves #307 quota error mapping",
         "Register error code E4103_LEASE_EXPIRED", "Resolves #408 lease error mapping", 55, 56,
         "ERROR_TABLE.register_code(4102, ErrorSpec(status=429, retryable=True))\n",
         "ERROR_TABLE.register_code(4103, ErrorSpec(status=409, retryable=True))\n"),
        (309, 410, "Add metric histogram rpc_decode_latency", "Fixes #309 decode latency metric",
         "Add metric histogram rpc_sign_latency", "Fixes #410 signing latency metric", 32, 33,
         "METRICS.register_histogram('rpc_decode_latency', HistogramSpec(unit='ms'))\n",
         "METRICS.register_histogram('rpc_sign_latency', HistogramSpec(unit='ms'))\n"),
        (311, 412, "Mount gRPC service HealthCheckService", "Fixes #311 health gRPC mount",
         "Mount gRPC service ReflectionService", "Fixes #412 reflection gRPC mount", 118, 119,
         "GRPC_ROUTER.register_service('health', ServiceSpec(factory=build_health_svc))\n",
         "GRPC_ROUTER.register_service('reflection', ServiceSpec(factory=build_refl_svc))\n"),
    ]

    pairs: list[tuple[str, bool, dict[str, object], dict[str, object]]] = []
    pr_id = 1000
    for t1, b1, t2, b2, fn, ln, add_c, del_c in cold_specs:
        a = make_pr(pr_id, t1, b1, "runtime", [(fn, [(ln, 4)], add_c, del_c)])
        b = make_pr(pr_id + 1, t2, b2, "runtime", [(fn, [(ln + 1, 4)], add_c, del_c)])
        pr_id += 2
        pairs.append(("symptom_vs_mechanism_cold", True, a, b))

    for t1, t2, b1, b2, fn, ln, add_c in paraphrase_specs:
        a = make_pr(pr_id, t1, b1, "core", [(fn, [(ln, 3)], add_c, "")])
        b = make_pr(pr_id + 1, t2, b2, "core", [(fn, [(ln, 3)], add_c, "")])
        pr_id += 2
        pairs.append(("paraphrased_dup", True, a, b))

    for _i1, _i2, t1, b1, t2, b2, l1, l2, c1, c2 in registry_nondup_specs:
        a = make_pr(pr_id, t1, b1, "registry", [("src/router/registry.py", [(l1, 3)], c1, "")])
        b = make_pr(pr_id + 1, t2, b2, "registry", [("src/router/registry.py", [(l2, 3)], c2, "")])
        pr_id += 2
        assert intrude_check_pattern_pinned(a, b) == -1
        pairs.append(("shared_registry_disjoint_issue", False, a, b))

    # Disjoint synthetic training split (30 pairs: 8 cold dups, 6 paraphrased dups,
    # 8 disjoint-file non-dups, 8 shared-registry disjoint-issue non-dups) for AdaBoost stumps
    train_pairs: list[tuple[bool, dict[str, object], dict[str, object]]] = []
    tr_id = 5000
    for k in range(8):
        add_a = f"if ctx is None: return guard_null_ptr(ctx, limit=64)\n"
        add_b = add_a if (k % 2 == 0) else f"guard_null_ptr(ctx, max_items=128, strict=True)\n"
        a = make_pr(
            tr_id,
            f"Symptom report alpha_{k} unexpected UI stall",
            f"Client screen stops responding during event_{k}",
            "train_rt",
            [(f"src/cold/mod_{k}.py", [(20 + k * 5, 4)], add_a, "pass\n")],
        )
        b = make_pr(
            tr_id + 1,
            f"Check null context pointer in mod_{k}",
            f"Invoke guard_null_ptr helper in handler_{k}",
            "train_rt",
            [(f"src/cold/mod_{k}.py", [(21 + k * 5, 4)], add_b, "pass\n")],
        )
        tr_id += 2
        train_pairs.append((True, a, b))
    for k in range(6):
        pat_body_a = f"Fixes #{600 + k} mutex lock around shard_{k} LRU pop" if k < 3 else f"Acquire mutex lock around shard_{k} LRU pop"
        pat_body_b = f"Resolves #{600 + k} acquire mutex in shard_{k} eviction" if k < 3 else f"Guard shard_{k} LRU eviction with mutex"
        add_ca = f"with shard_lock: entry = lru_ring.pop_oldest()\n"
        add_cb = add_ca if (k % 2 == 0) else f"with shard_lock: lru_ring.evict_tail(now_ts)\n"
        a = make_pr(
            tr_id,
            f"Fix cache eviction race in shard_{k}",
            pat_body_a,
            "train_core",
            [(f"src/cache/shard_{k}.py", [(30, 3)], add_ca, "")],
        )
        b = make_pr(
            tr_id + 1,
            f"Prevent shard_{k} LRU pop race condition",
            pat_body_b,
            "train_core",
            [(f"src/cache/shard_{k}.py", [(30, 3)], add_cb, "")],
        )
        tr_id += 2
        train_pairs.append((True, a, b))
    for k in range(8):
        a = make_pr(
            tr_id,
            f"Parse AST operator precedence_{k}",
            f"Handle grammar token_{k} in lexer",
            "train_parser",
            [(f"src/parser/rule_{k}.py", [(10, 4)], f"parse_node_{k}(stream)\n", "")],
        )
        b = make_pr(
            tr_id + 1,
            f"Compact SQL B-tree page_{k}",
            f"Vacuum dead tuples in storage_{k}",
            "train_db",
            [(f"src/db/index_{k}.py", [(90, 4)], f"plan.use_index(idx_{k})\n", "")],
        )
        tr_id += 2
        train_pairs.append((False, a, b))
    reg_verbs_a = ["Expose", "Mount", "Enable", "Declare", "Bind", "Attach", "Wire", "Publish"]
    reg_verbs_b = ["Support", "Register", "Configure", "Define", "Export", "Install", "Add", "Hook"]
    for k in range(8):
        a = make_pr(
            tr_id,
            f"{reg_verbs_a[k]} endpoint /v2/alpha_{k} handler",
            f"Fixes #{700 + 2 * k} alpha_{k} route entry",
            "train_reg",
            [("src/cli/table.py", [(50 + k * 4, 3)], f"TABLE.register_route('alpha_{k}', RouteSpec(handler=run_a, auth='token'))\n", "")],
        )
        b = make_pr(
            tr_id + 1,
            f"{reg_verbs_b[k]} route /v2/beta_{k} spec",
            f"Closes #{800 + 2 * k} beta_{k} webhook spec",
            "train_reg",
            [("src/cli/table.py", [(51 + k * 4, 3)], f"TABLE.register_route('beta_{k}', RouteSpec(handler=run_b, auth='token'))\n", "")],
        )
        tr_id += 2
        train_pairs.append((False, a, b))

    all_prs = [p for _, _, a, b in pairs for p in (a, b)]
    train_prs = [p for _, a, b in train_pairs for p in (a, b)]
    combined_prs = train_prs + all_prs
    text_corpus = TfIdfCorpus([intrude_tokenize(f"{p['title']} {p['body']}") for p in combined_prs])
    code_corpus = TfIdfCorpus(
        [
            intrude_tokenize(" ".join(f["add_code"] for f in p["file_list"]))  # type: ignore[index]
            for p in combined_prs
        ]
    )

    # Build text-only BM25F_ext unigram (avg_u) and bigram (avg_b) statistics cleanly
    uni_df: Counter[str] = Counter()
    bi_df: Counter[str] = Counter()
    uni_sum_lens: list[int] = []
    uni_desc_lens: list[int] = []
    bi_sum_lens: list[int] = []
    bi_desc_lens: list[int] = []
    for p in all_prs:
        st = intrude_tokenize(str(p["title"]))
        dt = intrude_tokenize(str(p["body"]))[:400]
        st_bi = [f"{st[i]}_{st[i + 1]}" for i in range(len(st) - 1)]
        dt_bi = [f"{dt[i]}_{dt[i + 1]}" for i in range(len(dt) - 1)]
        uni_sum_lens.append(len(st))
        uni_desc_lens.append(len(dt))
        bi_sum_lens.append(len(st_bi))
        bi_desc_lens.append(len(dt_bi))
        for u in set(st + dt):
            uni_df[u] += 1
        for bg in set(st_bi + dt_bi):
            bi_df[bg] += 1
    n_tot = len(all_prs)
    uni_idf = {k: math.log((n_tot + 1.0) / (v + 0.5)) for k, v in uni_df.items()}
    bi_idf = {k: math.log((n_tot + 1.0) / (v + 0.5)) for k, v in bi_df.items()}
    avg_u = (sum(uni_sum_lens) / n_tot, sum(uni_desc_lens) / n_tot)
    avg_b = (sum(bi_sum_lens) / n_tot, sum(bi_desc_lens) / n_tot)

    def exact_intrude_9vec(a: dict[str, object], b: dict[str, object], use_pattern: bool) -> list[float]:
        """Exact 9-scalar sim_to_vet vector from luyaor/INTRUDE@87a69cbb comp.py:274-341."""
        t_sim = text_corpus.cosine(Counter(intrude_tokenize(str(a["title"]))), Counter(intrude_tokenize(str(b["title"]))))
        d_sim = text_corpus.cosine(
            Counter(intrude_tokenize(str(a["body"])[:2000])),
            Counter(intrude_tokenize(str(b["body"])[:2000])),
        )
        fa = [x["name"] for x in a["file_list"]]  # type: ignore[index]
        fb = [x["name"] for x in b["file_list"]]  # type: ignore[index]
        file_sim = intrude_counter_similarity(Counter(fa), Counter(fb))
        ov_set = set(fa) & set(fb)
        ov_len = float(len(ov_set))

        def delta_counter(pr: dict[str, object]) -> Counter[str]:
            add_t: list[str] = []
            del_t: list[str] = []
            for f in pr["file_list"]:  # type: ignore[index]
                add_t.extend(intrude_tokenize(f["add_code"]))
                del_t.extend(intrude_tokenize(f["del_code"]))
            return intrude_get_delta_code_tokens_counter(add_t, del_t)

        a_ov = intrude_get_pull_on_overlap(a, ov_set)
        b_ov = intrude_get_pull_on_overlap(b, ov_set)
        code_glob = code_corpus.cosine(delta_counter(a), delta_counter(b))
        code_ov = code_corpus.cosine(delta_counter(a_ov), delta_counter(b_ov))
        loc_glob = intrude_location_similarity(intrude_get_location(a), intrude_get_location(b))
        loc_ov = intrude_location_similarity(intrude_get_location(a_ov), intrude_get_location(b_ov))
        pat = float(intrude_check_pattern_pinned(a, b)) if use_pattern else 0.0
        vec = [t_sim, d_sim, code_glob, code_ov, file_sim, ov_len, loc_glob, loc_ov, pat]
        assert len(vec) == 9
        return vec

    # Fit decision-stump AdaBoost on disjoint synthetic training split
    x_train = [exact_intrude_9vec(a, b, use_pattern=True) for _, a, b in train_pairs]
    y_train = [1 if is_dup else -1 for is_dup, _, _ in train_pairs]
    adaboost_stumps = train_decision_stump_adaboost(x_train, y_train, n_estimators=24, learning_rate=0.6)

    def linear_ablation_discriminator_9vec(v: list[float]) -> float:
        """[linear feature-ablation discriminator] with transparent fixed weights over sim_to_vet."""
        return (
            0.20 * (v[0] + v[1])
            + 0.35 * (v[2] + v[3])
            + 0.15 * (v[4] + min(1.0, v[5]))
            + 0.30 * (v[6] + v[7])
            + 1.10 * v[8]
        )

    text_tp = 0
    cold_text_tp = 0
    lin_tp = 0
    lin_fp_with_pat = 0
    lin_fp_no_pat = 0
    ada_tp = 0
    ada_fp_with_pat = 0
    ada_fp_no_pat = 0
    total_pos = sum(1 for _, is_dup, _, _ in pairs if is_dup)
    total_neg = sum(1 for _, is_dup, _, _ in pairs if not is_dup)

    for kind, is_dup, a, b in pairs:
        # Text-only BM25F_ext (unigram avg_u + bigram avg_b; excludes REP's 5 bug-tracker categorical fields)
        bm25_text = 0.7 * bm25f_ext_score(a, b, uni_idf, avg_u, 1) + 0.3 * bm25f_ext_score(a, b, bi_idf, avg_b, 2)
        pred_text = bm25_text >= 1.5

        v_on = exact_intrude_9vec(a, b, use_pattern=True)
        v_off = exact_intrude_9vec(a, b, use_pattern=False)

        pred_lin_on = linear_ablation_discriminator_9vec(v_on) >= 0.75
        pred_lin_off = linear_ablation_discriminator_9vec(v_off) >= 0.75
        pred_ada_on = adaboost_predict(adaboost_stumps, v_on)
        pred_ada_off = adaboost_predict(adaboost_stumps, v_off)

        if is_dup:
            if pred_text:
                text_tp += 1
                if kind == "symptom_vs_mechanism_cold":
                    cold_text_tp += 1
            if pred_lin_on:
                lin_tp += 1
            if pred_ada_on:
                ada_tp += 1
        else:
            if pred_lin_on:
                lin_fp_with_pat += 1
            if pred_lin_off:
                lin_fp_no_pat += 1
            if pred_ada_on:
                ada_fp_with_pat += 1
            if pred_ada_off:
                ada_fp_no_pat += 1

    text_recall = text_tp / total_pos
    lin_recall = lin_tp / total_pos
    ada_recall = ada_tp / total_pos

    assert cold_text_tp == 0, "Symptom-vs-mechanism cold duplicates have zero lexical overlap"
    assert abs(text_recall - (6.0 / 14.0)) < 1e-9
    assert abs(lin_recall - 1.0) < 1e-9 and lin_fp_with_pat == 0 and lin_fp_no_pat == total_neg == 6
    assert abs(ada_recall - 1.0) < 1e-9 and ada_fp_with_pat == 0 and ada_fp_no_pat == total_neg == 6

    return {
        "banner": banner,
        "intrude_feature_dim": 9,
        "pinned_check_pattern_audit_bugs": {
            "two_digit_shared_issue_42_pinned_vs_hardened": [pinned_e1, hard_e1],
            "two_digit_subset_42_105_pinned_vs_hardened": [pinned_e2, hard_e2],
            "disjoint_issues_shared_http_404_pinned_vs_hardened": [pinned_e3, hard_e3],
            "int_vs_str_self_pr_num_105_208_pinned_vs_hardened": [pinned_e4, hard_e4],
        },
        "text_only_bm25f_ext_unigram_bigram_recall_pct": round(text_recall * 100.0, 2),
        "cold_file_symptom_vs_mechanism_text_recall": f"{cold_text_tp}/8",
        "linear_feature_ablation_discriminator": {
            "label": "[linear feature-ablation discriminator]",
            "recall_pct": round(lin_recall * 100.0, 2),
            "shared_registry_fp_rate_with_check_pattern_pct": round(lin_fp_with_pat / total_neg * 100.0, 2),
            "shared_registry_fp_rate_ablation_pattern_off_pct": round(lin_fp_no_pat / total_neg * 100.0, 2),
        },
        "heldout_decision_stump_adaboost": {
            "label": "[trained decision-stump AdaBoost on disjoint 30-pair synthetic split]",
            "n_estimators": len(adaboost_stumps),
            "heldout_recall_pct": round(ada_recall * 100.0, 2),
            "heldout_shared_registry_fp_with_check_pattern_pct": round(ada_fp_with_pat / total_neg * 100.0, 2),
            "heldout_shared_registry_fp_ablation_pattern_off_pct": round(ada_fp_no_pat / total_neg * 100.0, 2),
        },
    }


# =============================================================================
# PROBE 3: Crystal Speculative Merge/Build/Test (Real Git + Scaling Simulation)
# =============================================================================


GIT_BIN = shutil.which("git", path="/usr/bin:/bin") or shutil.which("git") or "git"


def run_git(cwd: str, *args: str) -> subprocess.CompletedProcess[str]:
    env = {
        "PATH": "/usr/bin:/bin",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_AUTHOR_NAME": "ProbeBot",
        "GIT_AUTHOR_EMAIL": "probe@example.invalid",
        "GIT_COMMITTER_NAME": "ProbeBot",
        "GIT_COMMITTER_EMAIL": "probe@example.invalid",
        "HOME": cwd,
    }
    return subprocess.run(
        [GIT_BIN, *args],
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )


def verify_git_min_2_38() -> tuple[int, int]:
    ver_out = subprocess.check_output([GIT_BIN, "--version"], text=True).strip()
    m = re.search(r"(\d+)\.(\d+)", ver_out)
    assert m is not None, f"Cannot parse git version from {ver_out!r}"
    ver = (int(m.group(1)), int(m.group(2)))
    assert ver >= (2, 38), f"`git merge-tree --write-tree` requires Git >= 2.38, got {ver_out!r}"
    return ver


def static_compile_and_arity_check(repo_dir: Path) -> bool:
    """Deterministic static build gate: syntax compile + cross-module import/call arity check."""
    py_files = sorted((repo_dir / "pkg").glob("*.py"))
    exports: dict[str, dict[str, int]] = {}
    trees: dict[Path, ast.Module] = {}
    for pf in py_files:
        try:
            py_compile.compile(str(pf), doraise=True)
            src = pf.read_text(encoding="utf-8")
            tree = ast.parse(src, filename=pf.name)
        except Exception:
            return False
        trees[pf] = tree
        mod_defs: dict[str, int] = {}
        for node in tree.body:
            if isinstance(node, ast.FunctionDef):
                mod_defs[node.name] = len(node.args.args)
        exports[f"pkg.{pf.stem}"] = mod_defs

    for _pf, tree in trees.items():
        imported_arity: dict[str, int] = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and node.module in exports:
                mod_map = exports[node.module]
                for alias in node.names:
                    if alias.name not in mod_map:
                        return False
                    imported_arity[alias.asname or alias.name] = mod_map[alias.name]
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                fn = node.func.id
                if fn in imported_arity and len(node.args) != imported_arity[fn]:
                    return False
    return True


def execute_crystal_pipeline_real_git() -> dict[str, object]:
    """Part 3A: Real Git >= 2.38 execution inside TemporaryDirectory reproducing Crystal's lattice."""
    verify_git_min_2_38()
    with tempfile.TemporaryDirectory() as tmp_path_str:
        repo = Path(tmp_path_str) / "spec_repo"
        repo.mkdir()
        assert run_git(str(repo), "init", "-b", "main").returncode == 0
        assert run_git(str(repo), "config", "commit.gpgsign", "false").returncode == 0

        pkg = repo / "pkg"
        pkg.mkdir()
        (pkg / "__init__.py").write_text("", encoding="utf-8")
        (pkg / "pricing.py").write_text(
            "def compute_tax(subtotal: int) -> int:\n"
            "    return (subtotal * 10) // 100\n\n"
            "def apply_coupon(subtotal: int, pct: int) -> int:\n"
            "    discount = (subtotal * pct) // 100\n"
            "    return subtotal - discount\n",
            encoding="utf-8",
        )
        (pkg / "checkout.py").write_text(
            "from pkg.pricing import compute_tax, apply_coupon\n\n"
            "def final_total(subtotal: int, pct: int) -> int:\n"
            "    discounted = apply_coupon(subtotal, pct)\n"
            "    return discounted + compute_tax(discounted)\n",
            encoding="utf-8",
        )
        (pkg / "test_suite.py").write_text(
            "import unittest\n"
            "from pkg.checkout import final_total\n\n"
            "class CheckoutTest(unittest.TestCase):\n"
            "    def test_baseline(self) -> None:\n"
            "        self.assertEqual(final_total(100, 20), 88)\n",
            encoding="utf-8",
        )
        assert run_git(str(repo), "add", ".").returncode == 0
        assert run_git(str(repo), "commit", "-m", "base").returncode == 0

        def make_branch(name: str, edits: dict[str, str]) -> None:
            assert run_git(str(repo), "checkout", "-q", "-b", name, "main").returncode == 0
            for rel, content in sorted(edits.items()):
                (repo / rel).write_text(content, encoding="utf-8")
            assert run_git(str(repo), "add", ".").returncode == 0
            assert run_git(str(repo), "commit", "-q", "-m", name).returncode == 0

        make_branch(
            "tex_a",
            {
                "pkg/pricing.py": (
                    "def compute_tax(subtotal: int) -> int:\n"
                    "    return (subtotal * 8) // 100\n\n"
                    "def apply_coupon(subtotal: int, pct: int) -> int:\n"
                    "    discount = (subtotal * pct) // 100\n"
                    "    return subtotal - discount\n"
                )
            },
        )
        make_branch(
            "tex_b",
            {
                "pkg/pricing.py": (
                    "def compute_tax(subtotal: int) -> int:\n"
                    "    return (subtotal * 12) // 100\n\n"
                    "def apply_coupon(subtotal: int, pct: int) -> int:\n"
                    "    discount = (subtotal * pct) // 100\n"
                    "    return subtotal - discount\n"
                )
            },
        )
        make_branch(
            "build_a",
            {
                "pkg/pricing.py": (
                    "def compute_tax(subtotal: int, region_rate: int) -> int:\n"
                    "    return (subtotal * region_rate) // 100\n\n"
                    "def apply_coupon(subtotal: int, pct: int) -> int:\n"
                    "    discount = (subtotal * pct) // 100\n"
                    "    return subtotal - discount\n"
                ),
                "pkg/checkout.py": (
                    "from pkg.pricing import compute_tax, apply_coupon\n\n"
                    "def final_total(subtotal: int, pct: int) -> int:\n"
                    "    discounted = apply_coupon(subtotal, pct)\n"
                    "    return discounted + compute_tax(discounted, 10)\n"
                ),
            },
        )
        make_branch(
            "build_b",
            {
                "pkg/shipping.py": (
                    "from pkg.pricing import compute_tax\n\n"
                    "def shipping_with_tax(fee: int) -> int:\n"
                    "    return fee + compute_tax(fee)\n"
                )
            },
        )
        make_branch(
            "test_a",
            {
                "pkg/pricing.py": (
                    "def compute_tax(subtotal: int) -> int:\n"
                    "    return (subtotal * 10) // 100\n\n"
                    "def apply_coupon(subtotal: int, pct: int) -> int:\n"
                    "    return (subtotal * pct) // 100\n"
                ),
                "pkg/checkout.py": (
                    "from pkg.pricing import compute_tax, apply_coupon\n\n"
                    "def final_total(subtotal: int, pct: int) -> int:\n"
                    "    net = subtotal - apply_coupon(subtotal, pct)\n"
                    "    return net + compute_tax(net)\n"
                ),
            },
        )
        make_branch(
            "test_b",
            {
                "pkg/test_suite.py": (
                    "import unittest\n"
                    "from pkg.checkout import final_total\n"
                    "from pkg.pricing import apply_coupon\n\n"
                    "class CheckoutTest(unittest.TestCase):\n"
                    "    def test_baseline(self) -> None:\n"
                    "        self.assertEqual(final_total(100, 20), 88)\n"
                    "    def test_member_net_floor(self) -> None:\n"
                    "        self.assertEqual(max(50, apply_coupon(100, 15)), 85)\n"
                )
            },
        )
        make_branch(
            "clean_a",
            {
                "pkg/receipt.py": (
                    "from pkg.checkout import final_total\n\n"
                    "def format_receipt(subtotal: int, pct: int) -> str:\n"
                    "    return f'TOTAL={final_total(subtotal, pct)}'\n"
                )
            },
        )
        make_branch(
            "clean_b",
            {
                "pkg/test_suite.py": (
                    "import unittest\n"
                    "from pkg.checkout import final_total\n\n"
                    "class CheckoutTest(unittest.TestCase):\n"
                    "    def test_baseline(self) -> None:\n"
                    "        self.assertEqual(final_total(100, 20), 88)\n"
                    "        self.assertEqual(final_total(200, 0), 220)\n"
                )
            },
        )

        def classify_pair(br_mine: str, br_yours: str) -> tuple[str, bool, bool]:
            """Crystal AbstractStateChecker.java:348-535 modernized with Git >= 2.38 merge-tree."""
            sha_m = run_git(str(repo), "rev-parse", br_mine).stdout.strip()
            sha_y = run_git(str(repo), "rev-parse", br_yours).stdout.strip()
            if sha_m == sha_y:
                return "SAME", False, False
            if run_git(str(repo), "merge-base", "--is-ancestor", br_yours, br_mine).returncode == 0:
                return "AHEAD", False, False
            if run_git(str(repo), "merge-base", "--is-ancestor", br_mine, br_yours).returncode == 0:
                return "BEHIND", False, False

            # Zero-checkout in-memory merge probe (`git merge-tree --write-tree`, Git >= 2.38)
            mt = run_git(str(repo), "merge-tree", "--write-tree", br_mine, br_yours)
            if mt.returncode != 0:
                return "TEXTUAL_CONFLICT", False, False

            assert run_git(str(repo), "checkout", "-q", "-B", "_spec_merge", br_mine).returncode == 0
            mg = run_git(str(repo), "merge", "--no-edit", br_yours)
            assert mg.returncode == 0
            crystal_legacy_auto = "Auto-merging" in mg.stdout
            crystal_legacy_rec = "Merge made by recursive." in mg.stdout

            if not static_compile_and_arity_check(repo):
                return "BUILD_CONFLICT", crystal_legacy_auto, crystal_legacy_rec

            trun = subprocess.run(
                [sys.executable, "-I", "-B", "-m", "unittest", "discover", "-s", "pkg", "-t", ".", "-p", "test_*.py"],
                cwd=str(repo),
                capture_output=True,
                text=True,
                check=False,
            )
            if trun.returncode != 0:
                return "TEST_CONFLICT", crystal_legacy_auto, crystal_legacy_rec
            return "MERGE_CLEAN", crystal_legacy_auto, crystal_legacy_rec

        rel_same, _, _ = classify_pair("main", "main")
        rel_ahead, _, _ = classify_pair("clean_a", "main")
        rel_behind, _, _ = classify_pair("main", "clean_a")
        rel_tex, _, _ = classify_pair("tex_a", "tex_b")
        rel_build, _, _ = classify_pair("build_a", "build_b")
        rel_test, _, _ = classify_pair("test_a", "test_b")
        rel_clean, legacy_auto, legacy_rec = classify_pair("clean_a", "clean_b")

        assert (rel_same, rel_ahead, rel_behind) == ("SAME", "AHEAD", "BEHIND")
        assert rel_tex == "TEXTUAL_CONFLICT"
        assert rel_build == "BUILD_CONFLICT"
        assert rel_test == "TEST_CONFLICT"
        assert rel_clean == "MERGE_CLEAN"
        assert legacy_auto is False and legacy_rec is False

    assert not os.path.exists(tmp_path_str), "TemporaryDirectory must leave zero disk residue"
    return {
        "git_merge_tree_write_tree_min_version": "2.38",
        "lattice_outcomes": {
            "same": rel_same,
            "ahead": rel_ahead,
            "behind": rel_behind,
            "textual": rel_tex,
            "build_higher_order": rel_build,
            "test_higher_order": rel_test,
            "clean": rel_clean,
        },
        "crystal_2011_git_stdout_bug_confirmed": {
            "disjoint_merge_has_auto_merging_substr": legacy_auto,
            "modern_git_has_recursive_substr": legacy_rec,
        },
        "temp_dir_cleaned": True,
    }


def probe_crystal_speculative_merge_and_stc_gate() -> dict[str, object]:
    banner = (
        "[real git execution] + [exact reproduction of pinned repository logic] + "
        "[controlled combinatorial / simulation experiment]"
    )
    real_git_res = execute_crystal_pipeline_real_git()

    # Part 3B: Synthetic ring-coupled 28-module scaling simulation across N in {8, 16, 32, 64}
    # (25% uncommitted scratch buffers; uniform module sampling over 28 modules with 1-hop ring STC,
    # yielding at N=64 over 11,280 committed pairs: 95.79% clean, 1.84% textual, 0.66% build, 1.72% test).
    rng = random.Random(SEED)
    n_modules = 28
    scaling_rows: dict[str, dict[str, object]] = {}

    for n_agents in (8, 16, 32, 64):
        pairs_per_tick = n_agents * (n_agents - 1) // 2
        n_ticks = 10
        all_pairs_runs = 0
        committed_pairs = 0
        committed_clean = 0
        committed_textual = 0
        committed_build = 0
        committed_test = 0
        gated_runs = 0
        ho_total_committed = 0
        gated_ho_caught = 0
        uncommitted_false_aborts_naive = 0

        for tick in range(n_ticks):
            agents = []
            for a in range(n_agents):
                mod = rng.randrange(n_modules)
                committed = (a % 4) != 3  # 25% uncommitted scratch buffers (Sarma 2012 transient churn)
                edits_sig = rng.random() < 0.25
                edits_inv = rng.random() < 0.50
                agents.append((mod, committed, edits_sig, edits_inv))

            for i in range(n_agents):
                m_i, c_i, sig_i, inv_i = agents[i]
                for j in range(i + 1, n_agents):
                    m_j, c_j, sig_j, inv_j = agents[j]
                    all_pairs_runs += 1
                    same_mod = m_i == m_j
                    stc_coupled = abs(m_i - m_j) in (1, n_modules - 1)
                    rare_untracked = (
                        (not same_mod)
                        and (not stc_coupled)
                        and ((tick * 131 + i * 31 + j * 17 + 7) % 2400 == 0)
                    )

                    is_textual = same_mod and ((i + j + tick) % 2 == 0)
                    is_build = (not is_textual) and stc_coupled and (sig_i or sig_j) and ((i + j + tick) % 5 == 0)
                    is_test = (
                        (not is_textual)
                        and (not is_build)
                        and (
                            ((same_mod or stc_coupled) and (inv_i and inv_j))
                            or rare_untracked
                        )
                    )

                    if not (c_i and c_j):
                        if same_mod:
                            uncommitted_false_aborts_naive += 1
                        continue

                    committed_pairs += 1
                    if is_textual:
                        committed_textual += 1
                    elif is_build:
                        committed_build += 1
                        ho_total_committed += 1
                    elif is_test:
                        committed_test += 1
                        ho_total_committed += 1
                    else:
                        committed_clean += 1

                    if same_mod or stc_coupled:
                        gated_runs += 1
                        if is_build or is_test:
                            gated_ho_caught += 1

        assert ho_total_committed > 0, f"Non-vacuity required at N={n_agents}"
        committed_stc_reduction_pct = (1.0 - gated_runs / committed_pairs) * 100.0
        combined_reduction_pct = (1.0 - gated_runs / all_pairs_runs) * 100.0
        ho_recall_pct = gated_ho_caught / ho_total_committed * 100.0
        scaling_rows[f"N={n_agents}"] = {
            "pairs_per_tick": pairs_per_tick,
            "all_pairs_10ticks_incl_uncommitted": all_pairs_runs,
            "committed_pairs_10ticks": committed_pairs,
            "committed_conflict_rates_pct": {
                "clean": round(committed_clean / committed_pairs * 100.0, 2),
                "textual": round(committed_textual / committed_pairs * 100.0, 2),
                "build": round(committed_build / committed_pairs * 100.0, 2),
                "test": round(committed_test / committed_pairs * 100.0, 2),
            },
            "tier0_stc_gated_runs_10ticks": gated_runs,
            "committed_pair_stc_compute_reduction_pct": round(committed_stc_reduction_pct, 2),
            "combined_uncommitted_and_stc_compute_reduction_pct": round(combined_reduction_pct, 2),
            "committed_higher_order_conflicts": ho_total_committed,
            "vcs_textual_only_ho_recall_pct": 0.0,
            "tier0_gated_ho_recall_pct": round(ho_recall_pct, 2),
            "naive_uncommitted_false_aborts": uncommitted_false_aborts_naive,
        }

    r64 = scaling_rows["N=64"]
    assert r64["pairs_per_tick"] == 2016 and r64["all_pairs_10ticks_incl_uncommitted"] == 20160
    assert r64["committed_pairs_10ticks"] == 11280 and r64["tier0_stc_gated_runs_10ticks"] == 1221
    assert r64["committed_pair_stc_compute_reduction_pct"] == 89.18
    assert r64["combined_uncommitted_and_stc_compute_reduction_pct"] == 93.94
    assert r64["committed_conflict_rates_pct"] == {
        "clean": 95.79,
        "textual": 1.84,
        "build": 0.66,
        "test": 1.72,
    }
    assert r64["tier0_gated_ho_recall_pct"] == 99.63

    return {
        "banner": banner,
        "part_3a_real_git": real_git_res,
        "brun_2011_3repo_reconciled": {
            "merges_3repo_fig4": 1694,
            "merges_9repo_fig4": 3562,
            "prose_typo_in_brun_sec4_2": 5355,
            "higher_order_share_of_conflicts_pct": round((24 + 109) / 399 * 100.0, 2),
            "higher_order_share_of_clean_textual_merges_pct": round((24 + 109) / 1428 * 100.0, 2),
        },
        "part_3b_scaling": scaling_rows,
    }


# =============================================================================
# PROBE 4: Real 2-Watched-Literal 1-UIP CDCL Solver + LBD & AIMD Nogood Sharing
# =============================================================================


def build_configuration_repair_cnf(unsat: bool, seed: int = SEED) -> tuple[int, list[tuple[int, ...]], list[int], list[int]]:
    """Constructs a structured configuration-repair CNF (121 vars, 286 clauses when unsat=True)."""
    rng = random.Random(seed)
    clauses: list[tuple[int, ...]] = []
    n_roots = 14
    roots = list(range(1, n_roots + 1))
    nxt = n_roots + 1
    pos_leaf: dict[int, int] = {}
    neg_leaf: dict[int, int] = {}
    for r in roots:
        a1, a2 = nxt, nxt + 1
        nxt += 2
        b1, b2 = nxt, nxt + 1
        nxt += 2
        clauses += [(-r, a1), (-a1, a2), (r, b1), (-b1, b2)]
        pos_leaf[r] = a2
        neg_leaf[r] = b2

    for k in range(len(roots) - 1):
        u, v = roots[k], roots[k + 1]
        g = nxt
        nxt += 1
        clauses += [
            (-pos_leaf[u], -neg_leaf[v], g),
            (-pos_leaf[u], -neg_leaf[v], -g),
            (-neg_leaf[u], -pos_leaf[v], g),
            (-neg_leaf[u], -pos_leaf[v], -g),
        ]

    g0 = nxt
    nxt += 1
    clauses += [(-neg_leaf[1], -neg_leaf[n_roots], g0), (-neg_leaf[1], -neg_leaf[n_roots], -g0)]
    if unsat:
        g1 = nxt
        nxt += 1
        clauses += [(-pos_leaf[1], -pos_leaf[n_roots], g1), (-pos_leaf[1], -pos_leaf[n_roots], -g1)]

    core_vars = list(range(1, nxt))

    opt_roots: list[int] = []
    opt_d: dict[int, tuple[int, int]] = {}
    for _ in range(12):
        o = nxt
        d1 = nxt + 1
        d2 = nxt + 2
        nxt += 3
        opt_roots.append(o)
        opt_d[o] = (d1, d2)
        clauses += [(o, d1), (-d1, d2)]

    for _ in range(150):
        chosen = rng.sample(opt_roots, 5)
        lits: list[int] = []
        for o in chosen[:4]:
            d1, d2 = opt_d[o]
            lits.extend([-d1, -d2])
        lits.append(-opt_d[chosen[4]][0])
        assert len(lits) == 9
        clauses.append(tuple(lits))

    tot_vars = nxt - 1
    return tot_vars, clauses, core_vars, opt_roots


def build_wide_glue_fanout_cnf() -> tuple[int, list[tuple[int, ...]], list[list[int]]]:
    """Constructs a CNF where single level-1 hub decisions propagate 7 fanout literals,
    so 1-UIP conflict analysis learns genuine LBD = 2 glue clauses of width |C| = 8
    alongside width-2 glue clauses—exercising AIMD size throttling (|C| <= e_lim)
    simultaneously with LBD <= 2 filtering!
    """
    clauses: list[tuple[int, ...]] = []
    nxt = 1
    # 6 hub variables h_1..h_6: setting h_m = False propagates 7 distinct fanout literals f_{m,1..7}
    hubs: list[int] = []
    fanout: dict[int, list[int]] = {}
    for _ in range(6):
        h = nxt
        fs = list(range(nxt + 1, nxt + 8))
        nxt += 8
        hubs.append(h)
        fanout[h] = fs
        for f in fs:
            clauses.append((h, f))

    # Each probe trigger t_k (when False) conflicts against all 7 fanout literals of a hub h_m,
    # generating an 8-literal 1-UIP clause (-f_{m,1}, ..., -f_{m,7}, +p_k) with LBD = 2!
    triggers: list[int] = []
    for idx in range(24):
        h = hubs[idx % len(hubs)]
        t = nxt
        a = nxt + 1
        g = nxt + 2
        nxt += 3
        triggers.append(t)
        clauses.append((t, a))
        fs = fanout[h]
        clauses.append(tuple([-f for f in fs] + [-a, g]))
        clauses.append(tuple([-f for f in fs] + [-a, -g]))

    # Underlying 14-root 2-hop ABI UNSAT core so workers run multiple rounds while
    # exchanging and throttling width-8 LBD=2 glue clauses before proving UNSAT
    roots = list(range(nxt, nxt + 14))
    nxt += 14
    pos_leaf: dict[int, int] = {}
    neg_leaf: dict[int, int] = {}
    core_all: list[int] = list(roots)
    for r in roots:
        a1, a2, b1, b2 = nxt, nxt + 1, nxt + 2, nxt + 3
        nxt += 4
        core_all.extend([a1, a2, b1, b2])
        clauses += [(-r, a1), (-a1, a2), (r, b1), (-b1, b2)]
        pos_leaf[r] = a2
        neg_leaf[r] = b2
    for k in range(len(roots) - 1):
        u, v = roots[k], roots[k + 1]
        g = nxt
        nxt += 1
        core_all.append(g)
        clauses += [
            (-pos_leaf[u], -neg_leaf[v], g),
            (-pos_leaf[u], -neg_leaf[v], -g),
            (-neg_leaf[u], -pos_leaf[v], g),
            (-neg_leaf[u], -pos_leaf[v], -g),
        ]
    g0, g1 = nxt, nxt + 1
    nxt += 2
    core_all.extend([g0, g1])
    clauses += [
        (-neg_leaf[roots[0]], -neg_leaf[roots[-1]], g0),
        (-neg_leaf[roots[0]], -neg_leaf[roots[-1]], -g0),
        (-pos_leaf[roots[0]], -pos_leaf[roots[-1]], g1),
        (-pos_leaf[roots[0]], -pos_leaf[roots[-1]], -g1),
    ]

    tot_vars = nxt - 1
    used = set(hubs) | set(triggers) | set(core_all)
    rest = [v for v in range(1, tot_vars + 1) if v not in used]
    orders: list[list[int]] = []
    for w in range(4):
        rot_h = hubs[w:] + hubs[:w]
        rot_t = triggers[w * 4 :] + triggers[: w * 4]
        half = len(core_all) // 2
        rot_c = (core_all[:half] + core_all[half:]) if (w % 2 == 0) else list(reversed(core_all))
        orders.append(rot_h + rot_t + rot_c + rest)
    return tot_vars, clauses, orders


class MiniCDCLSolver:
    """Genuine 2-watched-literal 1-UIP CDCL solver with exact LBD (Audemard & Simon 2009)."""

    def __init__(
        self,
        num_vars: int,
        base_clauses: list[tuple[int, ...]],
        phase_pref: int,
        var_order: list[int],
    ) -> None:
        self.num_vars = num_vars
        self.phase_pref = phase_pref
        self.var_order = list(var_order)
        self.activity = {v: (len(var_order) - i) * 0.4 for i, v in enumerate(var_order)}
        self.var_inc = 1.0
        self.clauses: list[list[int]] = []
        self.watches: dict[int, list[int]] = {lit: [] for v in range(1, num_vars + 1) for lit in (v, -v)}
        self.known_clauses: set[tuple[int, ...]] = set()
        self.val: dict[int, bool] = {}
        self.level: dict[int, int] = {}
        self.reason: dict[int, list[int] | None] = {}
        self.trail: list[int] = []
        self.trail_lim: list[int] = []
        self.qhead = 0
        self.conflicts = 0
        self.bcp_lit_scans = 0
        self.lbd_hist: Counter[int] = Counter()
        self.exported: list[tuple[tuple[int, ...], int, bool]] = []
        self.imported_count = 0
        self.status: str | None = None

        for c in base_clauses:
            self.known_clauses.add(tuple(sorted(c)))
            lc = list(c)
            cid = len(self.clauses)
            self.clauses.append(lc)
            self.watches[-lc[0]].append(cid)
            self.watches[-lc[1]].append(cid)

    def lit_val(self, lit: int) -> bool | None:
        v = abs(lit)
        if v not in self.val:
            return None
        return self.val[v] if lit > 0 else (not self.val[v])

    def assign(self, lit: int, reason_clause: list[int] | None) -> None:
        v = abs(lit)
        self.val[v] = lit > 0
        self.level[v] = len(self.trail_lim)
        self.reason[v] = reason_clause
        self.trail.append(lit)

    def backtrack(self, target_level: int) -> None:
        if len(self.trail_lim) <= target_level:
            return
        cut = self.trail_lim[target_level]
        for lit in self.trail[cut:]:
            v = abs(lit)
            del self.val[v]
            del self.level[v]
            del self.reason[v]
        del self.trail[cut:]
        del self.trail_lim[target_level:]
        self.qhead = min(self.qhead, len(self.trail))

    def propagate(self) -> list[int] | None:
        while self.qhead < len(self.trail):
            p = self.trail[self.qhead]
            self.qhead += 1
            wlist = self.watches[p]
            i = 0
            while i < len(wlist):
                cid = wlist[i]
                c = self.clauses[cid]
                self.bcp_lit_scans += 1
                if c[0] == -p:
                    c[0], c[1] = c[1], c[0]
                first_val = self.lit_val(c[0])
                self.bcp_lit_scans += 1
                if first_val is True:
                    i += 1
                    continue
                moved = False
                for k in range(2, len(c)):
                    self.bcp_lit_scans += 1
                    if self.lit_val(c[k]) is not False:
                        c[1], c[k] = c[k], c[1]
                        self.watches[-c[1]].append(cid)
                        wlist[i] = wlist[-1]
                        wlist.pop()
                        moved = True
                        break
                if moved:
                    continue
                if first_val is False:
                    return c
                self.assign(c[0], c)
                i += 1
        return None

    def analyze_1uip(self, conflict_clause: list[int]) -> tuple[list[int], int, int]:
        cur_level = len(self.trail_lim)
        seen: set[int] = set()
        learnt_other: list[int] = []
        path_c = 0
        c: list[int] | None = conflict_clause
        idx = len(self.trail) - 1
        p = 0
        while True:
            assert c is not None
            for q in c:
                v = abs(q)
                if v == abs(p) or v in seen or self.level[v] == 0:
                    continue
                seen.add(v)
                self.activity[v] += self.var_inc
                if self.level[v] == cur_level:
                    path_c += 1
                else:
                    learnt_other.append(q)
            while abs(self.trail[idx]) not in seen:
                idx -= 1
            p = self.trail[idx]
            idx -= 1
            seen.remove(abs(p))
            path_c -= 1
            if path_c == 0:
                break
            c = self.reason[abs(p)]
        learnt = [-p] + sorted(learnt_other, key=lambda x: self.level[abs(x)], reverse=True)
        bt_level = self.level[abs(learnt[1])] if len(learnt) > 1 else 0
        lbd = max(1, len({self.level[abs(lit)] for lit in learnt if self.level[abs(lit)] > 0}))
        self.var_inc *= 1.05
        return learnt, bt_level, lbd

    def step_conflicts(self, max_conflicts: int) -> str | None:
        if self.status is not None:
            return self.status
        budget = max_conflicts
        while budget > 0:
            confl = self.propagate()
            if confl is not None:
                self.conflicts += 1
                budget -= 1
                if not self.trail_lim:
                    self.status = "UNSAT"
                    return "UNSAT"
                learnt, bt_level, lbd = self.analyze_1uip(confl)
                self.lbd_hist[lbd] += 1
                self.backtrack(bt_level)
                self.known_clauses.add(tuple(sorted(learnt)))
                if len(learnt) == 1:
                    self.assign(learnt[0], None)
                else:
                    cid = len(self.clauses)
                    self.clauses.append(learnt)
                    self.watches[-learnt[0]].append(cid)
                    self.watches[-learnt[1]].append(cid)
                    self.assign(learnt[0], learnt)
                self.exported.append((tuple(learnt), lbd, True))
            else:
                best_v = None
                best_act = -1.0
                for v in self.var_order:
                    if v not in self.val and self.activity[v] > best_act:
                        best_act = self.activity[v]
                        best_v = v
                if best_v is None:
                    self.status = "SAT"
                    return "SAT"
                self.trail_lim.append(len(self.trail))
                self.assign(best_v if self.phase_pref > 0 else -best_v, None)
        return None

    def import_clause(self, c_tup: tuple[int, ...]) -> None:
        if self.status is not None:
            return
        key = tuple(sorted(c_tup))
        if key in self.known_clauses:
            return
        self.known_clauses.add(key)
        self.imported_count += 1
        if len(c_tup) == 1:
            self.backtrack(0)
            if self.lit_val(c_tup[0]) is False:
                self.status = "UNSAT"
            elif self.lit_val(c_tup[0]) is None:
                self.assign(c_tup[0], None)
            return
        c = sorted(
            c_tup,
            key=lambda l: (
                0 if self.lit_val(l) is True else (1 if self.lit_val(l) is None else 2),
                -self.level.get(abs(l), 0),
            ),
        )
        if self.lit_val(c[0]) is not True and self.lit_val(c[1]) is False:
            self.backtrack(0)
            c = [l for l in c_tup if self.lit_val(l) is not False]
            if any(self.lit_val(l) is True for l in c_tup):
                return
            if not c:
                self.status = "UNSAT"
                return
            if len(c) == 1:
                self.assign(c[0], None)
                return
        cid = len(self.clauses)
        self.clauses.append(c)
        self.watches[-c[0]].append(cid)
        self.watches[-c[1]].append(cid)


def probe_cdcl_lbd_nogood_sharing() -> dict[str, object]:
    banner = (
        "[exact reproduction of pinned repository logic] + "
        "[controlled combinatorial / simulation experiment]"
    )

    def make_worker_orders(tot_v: int, core_vars: list[int], opt_roots: list[int]) -> list[list[int]]:
        rest = [v for v in range(1, tot_v + 1) if v not in set(core_vars) and v not in set(opt_roots)]
        half = len(core_vars) // 2
        orders: list[list[int]] = []
        for i in range(4):
            rloc = random.Random(SEED + 100 + i)
            opts = list(opt_roots)
            rloc.shuffle(opts)
            if i == 0:
                orders.append(opts[:8] + core_vars[:half] + opts[8:] + core_vars[half:] + rest)
            elif i == 1:
                orders.append(opts[:8] + core_vars[half:] + opts[8:] + core_vars[:half] + rest)
            elif i == 2:
                orders.append(opts + core_vars[::2] + core_vars[1::2] + rest)
            else:
                orders.append(opts + list(reversed(core_vars)) + rest)
        return orders

    # Part 4A: UNSAT multi-subsystem compatibility check comparing No-Share, Share-All,
    # AIMD-Size-Only (Hamadi 2009 aimdT: |C| <= e_lim without LBD filter), and Glue-AIMD
    tot_u, cls_u, core_u, opt_u = build_configuration_repair_cnf(unsat=True)
    orders_u = make_worker_orders(tot_u, core_u, opt_u)
    unsat_summary: dict[str, dict[str, object]] = {}

    for policy in ("no_share", "share_all", "aimd_size_only", "glue_aimd"):
        workers = [MiniCDCLSolver(tot_u, cls_u, phase_pref=-1, var_order=orders_u[i]) for i in range(4)]
        # Hamadi, Jabbour, & Sais (IJCAI 2009, pp. 500-502): e_0 = 8, b = 8 (increase), a = 0.125 (decrease)
        e_lim = [[8.0] * 4 for _ in range(4)]
        winner_outcome: str | None = None
        imported_lits = 0
        aimd_rejected = 0
        rounds = 0
        while rounds < 120:
            rounds += 1
            bufs = []
            for w in workers:
                w.exported.clear()
                res = w.step_conflicts(4)
                if res is None:
                    w.backtrack(0)
                bufs.append(list(w.exported))
                if res is not None and winner_outcome is None:
                    winner_outcome = res
            if winner_outcome is not None:
                break
            if policy == "no_share":
                continue
            for i in range(4):
                recv = 0
                for j in range(4):
                    if i == j:
                        continue
                    for c, lbd, verified in bufs[j]:
                        if policy == "share_all":
                            before = workers[i].imported_count
                            workers[i].import_clause(c)
                            if workers[i].imported_count > before:
                                imported_lits += len(c)
                            recv += 1
                        elif policy == "aimd_size_only" and verified:
                            if len(c) <= int(e_lim[j][i]):
                                before = workers[i].imported_count
                                workers[i].import_clause(c)
                                if workers[i].imported_count > before:
                                    imported_lits += len(c)
                                recv += 1
                            else:
                                aimd_rejected += 1
                        elif policy == "glue_aimd" and verified and lbd <= 2:
                            if len(c) <= int(e_lim[j][i]):
                                before = workers[i].imported_count
                                workers[i].import_clause(c)
                                if workers[i].imported_count > before:
                                    imported_lits += len(c)
                                recv += 1
                            else:
                                aimd_rejected += 1
                if policy in ("aimd_size_only", "glue_aimd"):
                    target_t = 2
                    for j in range(4):
                        if i == j:
                            continue
                        if recv < target_t:
                            e_lim[j][i] = e_lim[j][i] + 8.0 / max(1.0, e_lim[j][i])
                        elif recv > target_t:
                            e_lim[j][i] = max(2.0, e_lim[j][i] - 0.125 * e_lim[j][i])

        lbd_agg: Counter[int] = Counter()
        for w in workers:
            lbd_agg.update(w.lbd_hist)
        unsat_summary[policy] = {
            "outcome": winner_outcome,
            "rounds": rounds,
            "total_conflicts": sum(w.conflicts for w in workers),
            "bcp_literal_scans": sum(w.bcp_lit_scans for w in workers),
            "clauses_imported": sum(w.imported_count for w in workers),
            "imported_literal_volume": imported_lits,
            "aimd_size_rejected_clauses": aimd_rejected,
            "high_lbd_ge5_learned": sum(cnt for k, cnt in lbd_agg.items() if k >= 5),
            "glue_lbd_le2_learned": sum(cnt for k, cnt in lbd_agg.items() if k <= 2),
        }

    assert int(unsat_summary["no_share"]["high_lbd_ge5_learned"]) > 0  # type: ignore[arg-type]
    assert int(unsat_summary["aimd_size_only"]["aimd_size_rejected_clauses"]) > 0  # type: ignore[arg-type]
    assert unsat_summary["glue_aimd"]["outcome"] == "UNSAT"
    assert (
        int(unsat_summary["glue_aimd"]["bcp_literal_scans"])  # type: ignore[arg-type]
        < int(unsat_summary["share_all"]["bcp_literal_scans"])  # type: ignore[arg-type]
        < int(unsat_summary["no_share"]["bcp_literal_scans"])  # type: ignore[arg-type]
    )
    assert (
        int(unsat_summary["glue_aimd"]["imported_literal_volume"]) * 2  # type: ignore[arg-type]
        < int(unsat_summary["share_all"]["imported_literal_volume"])  # type: ignore[arg-type]
    )

    # Part 4B: Satisfiable configuration-repair instance testing unverified-nogood corruption vs verifier gate
    tot_s, cls_s, core_s, opt_s = build_configuration_repair_cnf(unsat=False)
    orders_s = make_worker_orders(tot_s, core_s, opt_s)
    sat_summary: dict[str, dict[str, object]] = {}

    for sat_policy in ("unverified_nogood_accepted", "verifier_witness_gated"):
        workers = [MiniCDCLSolver(tot_s, cls_s, phase_pref=-1, var_order=orders_s[i]) for i in range(4)]
        outcome = "TIMEOUT"
        quarantined_unverified = 0
        rounds = 0
        while rounds < 120:
            rounds += 1
            bufs = []
            for w in workers:
                w.exported.clear()
                res = w.step_conflicts(2)
                bufs.append(list(w.exported))
                if res == "SAT":
                    ok = all(
                        any((w.val[abs(lit)] if lit > 0 else not w.val[abs(lit)]) for lit in c)
                        for c in cls_s
                    )
                    assert ok
                    outcome = "VERIFIED_SAT_PATCH"
                    break
            if outcome == "VERIFIED_SAT_PATCH":
                break
            if all(w.status == "UNSAT" for w in workers):
                outcome = "FALSE_UNSAT_CORRUPTION"
                break

            if rounds == 1:
                bufs[3].append(((-1,), 1, False))
                if sat_policy == "unverified_nogood_accepted":
                    workers[3].import_clause((-1,))

            for i in range(4):
                for j in range(4):
                    if i == j:
                        continue
                    for c, lbd, verified in bufs[j]:
                        if not verified:
                            if sat_policy == "verifier_witness_gated":
                                quarantined_unverified += 1
                                continue
                        if lbd <= 2 and len(c) <= 8:
                            workers[i].import_clause(c)

        sat_summary[sat_policy] = {
            "outcome": outcome,
            "rounds": rounds,
            "quarantined_as_advisory_hypothesis": quarantined_unverified,
        }

    assert sat_summary["unverified_nogood_accepted"]["outcome"] == "FALSE_UNSAT_CORRUPTION"
    assert sat_summary["verifier_witness_gated"]["outcome"] == "VERIFIED_SAT_PATCH"
    assert int(sat_summary["verifier_witness_gated"]["quarantined_as_advisory_hypothesis"]) == 3  # type: ignore[arg-type]

    # Part 4C: Wide-glue fanout AIMD sub-check (LBD <= 2 clauses with |C| = 7 under congestion target T = 1)
    tot_f, cls_f, orders_f = build_wide_glue_fanout_cnf()
    fanout_workers = [MiniCDCLSolver(tot_f, cls_f, phase_pref=-1, var_order=orders_f[i]) for i in range(4)]
    e_lim_f = [[8.0] * 4 for _ in range(4)]
    min_e_lim_seen = 8.0
    aimd_filtered_lbd2 = 0
    accepted_lbd2 = 0
    wide_lbd2_seen = 0
    fanout_outcome: str | None = None
    for _rnd in range(40):
        f_bufs = []
        for w in fanout_workers:
            w.exported.clear()
            res = w.step_conflicts(4)
            if res is None:
                w.backtrack(0)
            f_bufs.append(list(w.exported))
            if res is not None and fanout_outcome is None:
                fanout_outcome = res
        if fanout_outcome is not None:
            break
        for i in range(4):
            recv = 0
            for j in range(4):
                if i == j:
                    continue
                for c, lbd, verified in f_bufs[j]:
                    if verified and lbd <= 2:
                        if len(c) >= 6:
                            wide_lbd2_seen += 1
                        if len(c) <= int(e_lim_f[j][i]):
                            fanout_workers[i].import_clause(c)
                            accepted_lbd2 += 1
                            recv += 1
                        else:
                            aimd_filtered_lbd2 += 1
            # Congestion target T = 1 import/round exercises AIMD decrease (-0.125*e) and recovery (+8/e)
            target_t = 1
            for j in range(4):
                if i == j:
                    continue
                if recv < target_t:
                    e_lim_f[j][i] = e_lim_f[j][i] + 8.0 / max(1.0, e_lim_f[j][i])
                elif recv > target_t:
                    e_lim_f[j][i] = max(2.0, e_lim_f[j][i] - 0.125 * e_lim_f[j][i])
                min_e_lim_seen = min(min_e_lim_seen, e_lim_f[j][i])

    assert fanout_outcome == "UNSAT"
    assert wide_lbd2_seen > 0 and aimd_filtered_lbd2 > 0 and min_e_lim_seen < 7.0

    return {
        "banner": banner,
        "part_4a_unsat_portfolio": unsat_summary,
        "part_4b_sat_unverified_nogood_hazard": sat_summary,
        "part_4c_wide_glue_aimd_subcheck": {
            "outcome": fanout_outcome,
            "wide_lbd_le2_candidates_len_ge6": wide_lbd2_seen,
            "accepted_lbd_le2_clauses": accepted_lbd2,
            "aimd_filtered_lbd_le2_clauses_gt_elim": aimd_filtered_lbd2,
            "min_e_lim_reached": round(min_e_lim_seen, 4),
        },
    }


# =============================================================================
# PROBE 5: GPTCache & vCache & ChatDev Blackboard vs. Hybrid Merkle Ledger
# =============================================================================

# Exact variance_map from vcache-project/vCache@50694eeb verified.py:473-517
VCACHE_VARIANCE_MAP: dict[int, float] = {
    6: 0.035445,
    7: 0.028285,
    8: 0.026436,
    9: 0.021349,
    10: 0.019371,
    11: 0.012615,
    12: 0.011433,
    13: 0.010228,
    14: 0.009963,
    15: 0.009253,
    16: 0.011674,
    20: 0.013081,
    31: 0.004570,
    40: 0.005233,
    48: 0.015310,
}


def sigmoid(z: float) -> float:
    if z >= 0.0:
        ez = math.exp(-min(z, 500.0))
        return 1.0 / (1.0 + ez)
    ez = math.exp(max(z, -500.0))
    return ez / (1.0 + ez)


def fit_unregularized_logistic_2d(sims: list[float], labels: list[int]) -> tuple[float, float]:
    """Exact 2-parameter unregularized logistic MLE matching verified.py:469-471, 607-610."""
    b0, b1 = 0.0, 1.0
    for _ in range(180):
        g0 = g1 = h00 = h01 = h11 = 0.0
        for x, y in zip(sims, labels):
            p = sigmoid(b0 + b1 * x)
            diff = y - p
            w = p * (1.0 - p)
            g0 += diff
            g1 += diff * x
            h00 += w
            h01 += w * x
            h11 += w * x * x
        det = h00 * h11 - h01 * h01
        if det < 1e-16 or (abs(g0) < 1e-9 and abs(g1) < 1e-9):
            break
        db0 = (h11 * g0 - h01 * g1) / det
        db1 = (-h01 * g0 + h00 * g1) / det
        step = math.hypot(db0, db1)
        if step > 4.0:
            db0 *= 4.0 / step
            db1 *= 4.0 / step
        b0 += db0
        b1 += db1
        if abs(b0) > 400.0 or abs(b1) > 400.0:
            break
    return b0, b1


def gptcache_is_hit(
    rank: float,
    min_rank: float = 0.0,
    max_rank: float = 1.0,
    similarity_threshold: float = 0.8,
    cache_factor: float = 1.0,
) -> bool:
    """Exact zilliztech/GPTCache@a74ac654 gptcache/adapter/adapter.py:98-107, 173."""
    rank_threshold = (max_rank - min_rank) * similarity_threshold * cache_factor
    rank_threshold = (
        max_rank
        if rank_threshold > max_rank
        else min_rank
        if rank_threshold < min_rank
        else rank_threshold
    )
    return rank_threshold <= rank


@dataclass
class VCacheMetadataExact:
    """Exact EmbeddingMetadataObj from vCache@50694eeb embedding_metadata_obj.py:37-59."""

    embedding_id: int
    response: str
    observations: list[tuple[float, int]]
    gamma: float | None = None
    t_hat: float | None = None
    t_prime: float | None = None
    var_t: float | None = None

    @classmethod
    def create(cls, embedding_id: int, response: str) -> VCacheMetadataExact:
        return cls(embedding_id=embedding_id, response=response, observations=[(0.0, 0), (1.0, 1)])


class VCacheAlgorithmExact:
    """Exact _Algorithm + __perform_cache_update from vCache@50694eeb verified.py:233, 418-759."""

    def __init__(self, delta: float = 0.01, seed: int = SEED) -> None:
        self.delta = delta
        self.p_c = 1.0 - delta
        self.epsilon_grid = [1e-6 + i * (1.0 - 2e-6) / 49.0 for i in range(50)]
        self.rng = random.Random(seed)
        self.store: list[tuple[str, VCacheMetadataExact]] = []
        self.next_id = 100

    def add_entry(self, prompt_key: str, response: str, existing: VCacheMetadataExact | None = None) -> VCacheMetadataExact:
        if existing is not None:
            self.store.append((prompt_key, existing))
            return existing
        meta = VCacheMetadataExact.create(self.next_id, response)
        self.next_id += 1
        self.store.append((prompt_key, meta))
        return meta

    def perform_cache_update_on_explore(
        self,
        prompt_key: str,
        nn_meta: VCacheMetadataExact,
        similarity_score: float,
        ground_truth_response: str,
    ) -> VCacheMetadataExact | None:
        """Exact verified.py:418-433 __perform_cache_update on EXPLORE:
        appends (s, is_correct) to nn_meta AND, if not is_correct, calls self.cache.add(...)
        without evicting nn_meta—creating duplicate identical vectors at s = 1.0!
        """
        is_correct = int(ground_truth_response == nn_meta.response)
        nn_meta.observations.append((round(similarity_score, 3), is_correct))
        if not is_correct:
            return self.add_entry(prompt_key, ground_truth_response)
        return None

    def estimate_and_tau(self, similarity_score: float, meta: VCacheMetadataExact) -> tuple[str, float]:
        s = round(similarity_score, 3)
        if len(meta.observations) < 6:
            return "EXPLORE", 1.0

        sims = [o[0] for o in meta.observations]
        labels = [o[1] for o in meta.observations]
        intercept, gamma = fit_unregularized_logistic_2d(sims, labels)
        gamma = max(gamma, 1e-6)
        t_hat = max(0.0, min(1.0, -intercept / gamma))

        min_pos = min(x for x, y in meta.observations if y == 1)
        max_neg = max(x for x, y in meta.observations if y == 0)
        perfect_sep = min_pos > max_neg

        if perfect_sep:
            n_obs = len(sims)
            var_t = VCACHE_VARIANCE_MAP.get(n_obs, VCACHE_VARIANCE_MAP[48])
        else:
            h00 = h01 = h11 = 0.0
            for x in sims:
                p = sigmoid(intercept + gamma * x)
                w = p * (1.0 - p)
                h00 += w
                h01 += w * x
                h11 += w * x * x
            det = max(1e-18, h00 * h11 - h01 * h01)
            inv00, inv01, inv11 = h11 / det, -h01 / det, h00 / det
            g0, g1 = -1.0 / gamma, intercept / (gamma * gamma)
            var_t = max(0.0, g0 * (inv00 * g0 + inv01 * g1) + g1 * (inv01 * g0 + inv11 * g1))

        t_hat_r = round(t_hat, 3)
        gamma_r = round(gamma, 3)
        meta.gamma = gamma_r
        meta.t_hat = t_hat_r
        meta.var_t = var_t

        taus: list[float] = []
        t_primes: list[float] = []
        for eps in self.epsilon_grid:
            z_q = STANDARD_NORMAL.inv_cdf(1.0 - eps)
            tp = max(0.0, min(1.0, t_hat_r + z_q * math.sqrt(var_t)))
            t_primes.append(tp)
            lik = sigmoid(gamma_r * (s - tp))
            alpha_lb = (1.0 - eps) * lik
            taus.append(1.0 - (1.0 - self.p_c) / (1.0 - alpha_lb))

        min_idx = min(range(len(taus)), key=lambda idx: taus[idx])
        meta.t_prime = t_primes[min_idx]
        tau = round(taus[min_idx], 5)
        u = self.rng.uniform(0.0, 1.0)
        return ("EXPLORE" if u <= tau else "EXPLOIT"), tau


class ChatDevBlackboardExact:
    """Exact OpenBMB/ChatDev@464a681b runtime/node/agent/memory/blackboard_memory.py:61-75."""

    def __init__(self, max_items: int = 100) -> None:
        self.max_items = max_items
        self.contents: list[dict[str, str]] = []

    def update(self, role: str, text: str) -> None:
        if text.strip():
            self.contents.append({"role": role, "content": text.strip()})
            self.contents = self.contents[-self.max_items :]

    def retrieve(self, query: str, top_k: int, similarity_threshold: float) -> list[dict[str, str]]:
        _ = (query, similarity_threshold)
        if not self.contents:
            return []
        if top_k <= 0 or top_k >= len(self.contents):
            return list(self.contents)
        return list(self.contents[-top_k:])


@dataclass(frozen=True)
class LedgerRecord:
    topic_id: str
    scope_key: tuple[str, str]                   # (toolchain_id, cfg_flags)
    dep_cone_blobs: tuple[tuple[str, str], ...]  # sorted (path, blob_sha256)
    dep_cone_merkle: str
    verifier_status: str                         # "VERIFIED" or "HYPOTHESIS"
    payload: str


def merkle_digest(blobs: dict[str, str], paths: list[str]) -> tuple[tuple[tuple[str, str], ...], str]:
    pairs = tuple((p, hashlib.sha256(blobs[p].encode("utf-8")).hexdigest()) for p in sorted(paths))
    h = hashlib.sha256()
    for p, oid in pairs:
        h.update(f"{p}:{oid}\n".encode("utf-8"))
    return pairs, h.hexdigest()


class HybridMerkleFindingsLedger:
    """2-Stage Candidate Discovery + Deterministic Merkle-Cone Freshness & Verifier Gate."""

    def __init__(self) -> None:
        self.records: list[LedgerRecord] = []

    def put(
        self,
        topic_id: str,
        scope_key: tuple[str, str],
        repo_blobs: dict[str, str],
        cone_paths: list[str],
        verifier_status: str,
        payload: str,
    ) -> None:
        pairs, digest = merkle_digest(repo_blobs, cone_paths)
        self.records.append(
            LedgerRecord(
                topic_id=topic_id,
                scope_key=scope_key,
                dep_cone_blobs=pairs,
                dep_cone_merkle=digest,
                verifier_status=verifier_status,
                payload=payload,
            )
        )

    def lookup(
        self,
        topic_id: str,
        scope_key: tuple[str, str],
        curr_blobs: dict[str, str],
    ) -> tuple[str, str | None, list[str]]:
        candidates = [r for r in reversed(self.records) if r.topic_id == topic_id and r.scope_key == scope_key]
        if not candidates:
            return "MISS", None, []
        rec = candidates[0]
        if rec.verifier_status != "VERIFIED":
            return "QUARANTINED_HYPOTHESIS", rec.payload, []

        # Map current live blobs to SHA-256 OIDs; use curr_oids.get(p) == recorded_oid so
        # deleted or renamed files return None != recorded_oid cleanly without KeyError.
        curr_oids = {p: hashlib.sha256(v.encode("utf-8")).hexdigest() for p, v in curr_blobs.items()}
        drifted = [
            p
            for p, recorded_oid in rec.dep_cone_blobs
            if not (curr_oids.get(p) == recorded_oid)
        ]
        if not drifted:
            return "AUTHORITATIVE_HIT", rec.payload, []
        if len(drifted) < len(rec.dep_cone_blobs):
            return "STALE_ADVISORY", rec.payload, drifted
        return "INVALIDATED_MISS", None, drifted


def probe_gptcache_vcache_vs_merkle_ledger() -> dict[str, object]:
    banner = (
        "[exact reproduction of pinned repository logic] + "
        "[controlled combinatorial / simulation experiment]"
    )

    repo_h0 = {
        "src/framing.rs": "pub fn parse_header(buf: &[u8]) -> u8 { buf[0] }\n",
        "src/header.rs": "pub const MAGIC: u8 = 0x7F;\n",
    }
    mode_a_stream = [
        (("rustc-1.82", "--no-default-features"), 1.000, "PANICS_ON_EMPTY=true"),
        (("rustc-1.82", "--all-features"), 0.962, "PANICS_ON_EMPTY=false"),
        (("rustc-1.82", "--no-default-features"), 1.000, "PANICS_ON_EMPTY=true"),
        (("rustc-nightly", "--all-features"), 0.951, "PANICS_ON_EMPTY=false"),
        (("rustc-1.82", "--no-default-features"), 1.000, "PANICS_ON_EMPTY=true"),
    ]

    gpt_mode_a_hits = 0
    gpt_mode_a_false_hits = 0
    gpt_cached_ans = mode_a_stream[0][2]
    for _scope, cos_sim, truth in mode_a_stream[1:]:
        if gptcache_is_hit(cos_sim, 0.0, 1.0, 0.80, 1.0):
            gpt_mode_a_hits += 1
            if gpt_cached_ans != truth:
                gpt_mode_a_false_hits += 1

    vc_algo = VCacheAlgorithmExact(delta=0.01, seed=SEED)
    vc_meta_a = VCacheMetadataExact.create(embedding_id=1, response=mode_a_stream[0][2])
    vc_mode_a_hits = 0
    for _, cos_sim, truth in mode_a_stream[1:]:
        act, _ = vc_algo.estimate_and_tau(cos_sim, vc_meta_a)
        if act == "EXPLOIT":
            vc_mode_a_hits += 1
        else:
            vc_meta_a.observations.append((round(cos_sim, 3), int(truth == vc_meta_a.response)))

    ledger = HybridMerkleFindingsLedger()
    merkle_mode_a_hits = 0
    merkle_mode_a_false_hits = 0
    for scope, _, truth in mode_a_stream:
        status, ans, _ = ledger.lookup("parse_header_empty", scope, repo_h0)
        if status == "AUTHORITATIVE_HIT":
            merkle_mode_a_hits += 1
            if ans != truth:
                merkle_mode_a_false_hits += 1
        else:
            ledger.put("parse_header_empty", scope, repo_h0, ["src/framing.rs"], "VERIFIED", truth)

    assert gpt_mode_a_hits == 4 and gpt_mode_a_false_hits == 2
    assert vc_mode_a_hits == 0 and len(vc_meta_a.observations) == 6
    assert merkle_mode_a_hits == 2 and merkle_mode_a_false_hits == 0

    # 2. Mode B: World-State Mutation H0 -> H1 on `src/framing.rs` at identical prompt cos = 1.000
    # Regime B1 (n = 6 separable observations at H0, var_t = 0.035445):
    # - Query 1 at H1 has tau(1.0) = 0.64878 (35.12% immediate stale hit risk, 64.88% EXPLORE).
    # - Upon the first EXPLORE, verified.py:418-433 appends (1.0, 0) to the H0 entry (jumping its
    #   tau(1.0) to 0.98000) AND calls self.cache.add(...) without evicting the H0 entry, creating
    #   2 duplicate identical embeddings at s = 1.0 with undefined get_knn(k=1) tie-breaking!
    prompt_key = "does_parse_header_panic_on_empty_slice"
    vc_meta_b1 = vc_algo.add_entry(
        prompt_key,
        "PANICS_ON_EMPTY=true",
        VCacheMetadataExact.create(embedding_id=2, response="PANICS_ON_EMPTY=true"),
    )
    for s_obs in (1.0, 1.0, 0.99, 0.98):
        vc_meta_b1.observations.append((s_obs, 1))
    assert len(vc_meta_b1.observations) == 6
    _, tau_b1_query1 = vc_algo.estimate_and_tau(1.000, vc_meta_b1)
    p_stale_b1_query1 = round(1.0 - max(0.0, min(1.0, tau_b1_query1)), 5)

    dup_h1_meta = vc_algo.perform_cache_update_on_explore(
        prompt_key, vc_meta_b1, 1.000, "PANICS_ON_EMPTY=false"
    )
    assert dup_h1_meta is not None
    _, tau_b1_old_after_explore = vc_algo.estimate_and_tau(1.000, vc_meta_b1)
    same_vec_entries = [m for k, m in vc_algo.store if k == prompt_key]
    assert len(same_vec_entries) == 2 and len(dup_h1_meta.observations) == 2
    assert abs(tau_b1_old_after_explore - 0.98) < 1e-4

    # Regime B2: Calibrated low-variance history at H0 (n = 18, var_t = 0.001818 -> raw tau(1.0) < 0):
    # P(EXPLORE) = 0.0 -> 100.0% permanent silent stale hits after H0 -> H1!
    vc_meta_b2 = VCacheMetadataExact.create(embedding_id=3, response="PANICS_ON_EMPTY=true")
    vc_meta_b2.observations.extend(
        [(0.45, 0), (0.52, 1), (0.55, 0), (0.50, 1), (0.40, 0), (0.60, 1)] + [(0.98, 1)] * 10
    )
    _, tau_b2_at_1 = vc_algo.estimate_and_tau(1.000, vc_meta_b2)
    repo_h1 = {
        "src/framing.rs": "pub fn parse_header(buf: &[u8]) -> u8 { buf.first().copied().unwrap_or(0) }\n",
        "src/header.rs": "pub const MAGIC: u8 = 0x7F;\n",
    }
    vc_b2_stale_hits = 0
    gpt_b_stale_hits = 0
    for _ in range(20):
        act_b2, _ = vc_algo.estimate_and_tau(1.000, vc_meta_b2)
        if act_b2 == "EXPLOIT":
            vc_b2_stale_hits += 1
        if gptcache_is_hit(1.000, 0.0, 1.0, 0.80, 1.0):
            gpt_b_stale_hits += 1

    st_single, _, drifted_single = ledger.lookup(
        "parse_header_empty", ("rustc-1.82", "--no-default-features"), repo_h1
    )
    ledger.put(
        "framing_magic_diag",
        ("rustc-1.82", "--no-default-features"),
        repo_h0,
        ["src/framing.rs", "src/header.rs"],
        "VERIFIED",
        "Check MAGIC framing offset in parse_header",
    )
    st_partial, _, drifted_partial = ledger.lookup(
        "framing_magic_diag", ("rustc-1.82", "--no-default-features"), repo_h1
    )

    # File-deletion check (`src/framing.rs` removed in H2 -> clean invalidation without KeyError)
    repo_h2_deleted = {"src/header.rs": repo_h1["src/header.rs"]}
    st_del_single, _, drifted_del_single = ledger.lookup(
        "parse_header_empty", ("rustc-1.82", "--no-default-features"), repo_h2_deleted
    )
    st_del_partial, _, drifted_del_partial = ledger.lookup(
        "framing_magic_diag", ("rustc-1.82", "--no-default-features"), repo_h2_deleted
    )

    # 3. ChatDev 2.0 BlackboardMemory recency-FIFO failure (`contents[-top_k:]` ignoring query & threshold)
    bb = ChatDevBlackboardExact(max_items=20)
    bb.update("Verifier", "VERIFIED: parse_header panics on empty slice at H0")
    for k in range(3):
        bb.update("Chatter", f"Unrelated CSS button padding note #{k}")
    bb_top3 = bb.retrieve(query="Does parse_header panic on empty slice?", top_k=3, similarity_threshold=0.99)
    bb_relevant_recalled = sum("parse_header" in item["content"] for item in bb_top3)

    assert abs(tau_b1_query1 - 0.64878) < 1e-5 and abs(p_stale_b1_query1 - 0.35122) < 1e-5
    assert tau_b2_at_1 < 0.0 and vc_b2_stale_hits == 20 and gpt_b_stale_hits == 20
    assert st_single == "INVALIDATED_MISS" and drifted_single == ["src/framing.rs"]
    assert st_partial == "STALE_ADVISORY" and drifted_partial == ["src/framing.rs"]
    assert st_del_single == "INVALIDATED_MISS" and drifted_del_single == ["src/framing.rs"]
    assert st_del_partial == "STALE_ADVISORY" and drifted_del_partial == ["src/framing.rs"]
    assert bb_relevant_recalled == 0

    return {
        "banner": banner,
        "mode_a_flag_aliasing_5queries": {
            "gptcache_hits_and_false_hits": [gpt_mode_a_hits, gpt_mode_a_false_hits],
            "vcache_cold_start_hits_in_5_queries": vc_mode_a_hits,
            "merkle_ledger_valid_hits_and_false_hits": [merkle_mode_a_hits, merkle_mode_a_false_hits],
        },
        "mode_b_world_state_mutation_cos_1_0": {
            "gptcache_stale_hit_rate_pct": round(gpt_b_stale_hits / 20 * 100.0, 2),
            "vcache_regime_b1_query1_tau_at_1_0": tau_b1_query1,
            "vcache_regime_b1_query1_stale_exploit_prob": p_stale_b1_query1,
            "vcache_regime_b1_post_explore_old_entry_tau_at_1_0": tau_b1_old_after_explore,
            "vcache_regime_b1_post_explore_duplicate_vectors_at_s_1_0": len(same_vec_entries),
            "vcache_regime_b1_post_explore_new_entry_obs_len": len(dup_h1_meta.observations),
            "vcache_regime_b2_calibrated_raw_tau_at_1_0": tau_b2_at_1,
            "vcache_regime_b2_stale_hit_rate_pct": round(vc_b2_stale_hits / 20 * 100.0, 2),
            "merkle_ledger_full_cone_status": st_single,
            "merkle_ledger_partial_cone_status": st_partial,
            "merkle_ledger_partial_drifted_files": drifted_partial,
            "merkle_ledger_deleted_file_statuses": [st_del_single, st_del_partial],
            "merkle_ledger_authoritative_stale_hits": 0,
        },
        "chatdev2_blackboard_fifo_top3_relevant_hits": bb_relevant_recalled,
    }


def main() -> None:
    t_start = time.perf_counter()
    results = {
        "probe_1_stc_and_palantir_impact": probe_stc_and_palantir_impact(),
        "probe_2_intrude_exact_features_and_dup_pr": probe_intrude_exact_features_and_dup_pr(),
        "probe_3_crystal_speculative_merge_and_stc_gate": probe_crystal_speculative_merge_and_stc_gate(),
        "probe_4_cdcl_lbd_nogood_sharing": probe_cdcl_lbd_nogood_sharing(),
        "probe_5_gptcache_vcache_vs_merkle_ledger": probe_gptcache_vcache_vs_merkle_ledger(),
    }
    elapsed = time.perf_counter() - t_start
    assert elapsed < 2.5, f"Probe suite exceeded 2.5s budget: {elapsed:.3f}s"

    script_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    canonical = json.dumps(results, indent=2, sort_keys=True)
    print(f"SCRIPT_SHA256={script_sha}")
    print(canonical)


if __name__ == "__main__":
    main()
