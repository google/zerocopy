#!/usr/bin/env python3
"""Deterministic Python 3.10+ stdlib verification suite for multi-agent trace
redundancy metrics and concurrent/shared-repository agent benchmark evaluators.

Verifies:
  1. Controlled file-granular causal-epoch trace decomposition (W_exec, W_disc,
     W_gen) using SHA-256 blob state equivalence, per-(agent, resource) causal
     backward slicing, callee-preserving AST alpha-normalization, partial-order
     DAG alignment over topological linearizations (Adriansyah et al. 2011), and
     DEFLATE 32 KiB sliding-window horizon breakdown vs. LZMA2 (Cebrian et al.
     2005; Cilibrasi & Vitanyi 2005).
  2. Exact ports of pinned benchmark evaluator scoring logic across MARBLE,
     Collab-Overcooked, TRAIL, MCPEval, AgentBoard, CooperBench (docker/modal vs.
     gcp_batch split-brain), SyncMind, and Commit0.
  3. Exact rank-correlation and renewal Cost-per-Solved (CPS) calculations on
     published tables from SyncMind (Table C1), TheAgentCompany (Table 1), and
     MCP-Bench (all 20 models), plus difficulty-stratified Simpson's paradox.

Zero third-party dependencies, zero disk writes, zero network access, and
bit-identical stdout across PYTHONHASHSEED values.
"""

from __future__ import annotations

import ast
import bisect
import collections
import dataclasses
import hashlib
import json
import lzma
import math
import zlib
from typing import Any, Sequence

EVIDENCE_EXPERIMENT = "[controlled trace-decomposition experiment]"
EVIDENCE_EVALUATOR = "[exact reproduction of pinned evaluator logic]"
EVIDENCE_TABLE = "[exact calculation on published benchmark table]"

DEFLATE_MAX_WINDOW_BYTES = 32768


# ============================================================================
# PROBE 1: Causal-Epoch 3-Regime Trace Decomposer (W_exec, W_disc, W_gen)
#          with Resource-Scoped SHA-256 Backward Slicing, Callee-Preserving AST
#          Skeleton, Partial-Order DAG Alignment, & DEFLATE vs. LZMA2 NCD Audit
# ============================================================================

@dataclasses.dataclass(frozen=True)
class TraceEvent:
    step: int
    agent: str
    kind: str  # "read" | "search" | "edit" | "test" | "hedge_test"
    resource: str  # canonical file, query key, or build/test target
    raw_tool: str
    raw_args: str
    tokens: int
    patch_code: str = ""  # Python snippet written for "edit" events
    blob_state: str | None = None  # optional explicit post-edit content ("__init__" reverts to v0)


def zlib_len(payload: bytes) -> int:
    """Raw DEFLATE byte length (wbits=-15, level=9, 32 KiB LZ77 sliding window)."""
    comp = zlib.compressobj(level=9, wbits=-15)
    return len(comp.compress(payload) + comp.flush())


def lzma_len(payload: bytes) -> int:
    """Raw LZMA2 byte length (preset=6, 8 MiB sliding dictionary)."""
    filters = [{"id": lzma.FILTER_LZMA2, "preset": 6}]
    return len(lzma.compress(payload, format=lzma.FORMAT_RAW, filters=filters))


def ncd_deflate(seq_a: Sequence[str], seq_b: Sequence[str]) -> float:
    """Unguarded DEFLATE Normalized Compression Distance (Cilibrasi & Vitanyi 2005)."""
    ba = ("\n".join(seq_a)).encode("utf-8")
    bb = ("\n".join(seq_b)).encode("utf-8")
    bab = ("\n".join( list(seq_a) + list(seq_b) )).encode("utf-8")
    ca, cb, cab = zlib_len(ba), zlib_len(bb), zlib_len(bab)
    return (cab - min(ca, cb)) / max(ca, cb, 1)


def ncd_window_guarded(seq_a: Sequence[str], seq_b: Sequence[str]) -> tuple[float, str]:
    """Window-guarded NCD: uses DEFLATE only when |x_a|+|x_b| <= 32 KiB, else LZMA2."""
    ba = ("\n".join(seq_a)).encode("utf-8")
    bb = ("\n".join(seq_b)).encode("utf-8")
    bab = ("\n".join(list(seq_a) + list(seq_b))).encode("utf-8")
    if len(bab) <= DEFLATE_MAX_WINDOW_BYTES:
        ca, cb, cab = zlib_len(ba), zlib_len(bb), zlib_len(bab)
        return (cab - min(ca, cb)) / max(ca, cb, 1), "deflate_32k"
    ca, cb, cab = lzma_len(ba), lzma_len(bb), lzma_len(bab)
    return (cab - min(ca, cb)) / max(ca, cb, 1), "lzma2_8m"


def ast_skeleton(code: str) -> str:
    """Alpha-normalizes bound local/parameter variables and string literals while
    preserving callee function and external global/attribute identifiers.
    """
    tree = ast.parse(code)
    local_map: dict[str, str] = {}

    def bind_local(name: str) -> str:
        if name not in local_map:
            local_map[name] = f"v{len(local_map)}"
        return local_map[name]

    # Collect bound parameters and local assignment targets in deterministic pre-order.
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for arg in (
                list(node.args.posonlyargs)
                + list(node.args.args)
                + list(node.args.kwonlyargs)
            ):
                bind_local(arg.arg)
            if node.args.vararg is not None:
                bind_local(node.args.vararg.arg)
            if node.args.kwarg is not None:
                bind_local(node.args.kwarg.arg)
        elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
            bind_local(node.id)

    class Normalizer(ast.NodeTransformer):
        def visit_FunctionDef(self, node: ast.FunctionDef) -> ast.AST:
            self.generic_visit(node)
            node.name = "FN"
            for arg in (
                list(node.args.posonlyargs)
                + list(node.args.args)
                + list(node.args.kwonlyargs)
            ):
                arg.arg = local_map[arg.arg]
            if node.args.vararg is not None:
                node.args.vararg.arg = local_map[node.args.vararg.arg]
            if node.args.kwarg is not None:
                node.args.kwarg.arg = local_map[node.args.kwarg.arg]
            return node

        def visit_Call(self, node: ast.Call) -> ast.AST:
            # Preserve external callee identifiers (foo(x) != bar(y)); only rename if
            # the callee itself is a bound parameter/local higher-order variable.
            if isinstance(node.func, ast.Name):
                if node.func.id in local_map:
                    node.func.id = local_map[node.func.id]
            else:
                node.func = self.visit(node.func)
            node.args = [self.visit(a) for a in node.args]
            node.keywords = [self.visit(kw) for kw in node.keywords]
            return node

        def visit_Name(self, node: ast.Name) -> ast.AST:
            if node.id in local_map:
                node.id = local_map[node.id]
            return node

        def visit_Constant(self, node: ast.Constant) -> ast.AST:
            if isinstance(node.value, str):
                node.value = "STR"
            return node

    norm = Normalizer().visit(tree)
    return ast.dump(norm, annotate_fields=True, include_attributes=False)


def linear_alignment_fitness(
    trace_ops: Sequence[str],
    model_path: Sequence[str],
) -> tuple[float, int, int]:
    """Unit-cost alignment fitness against a single sequential model path."""
    m, n = len(trace_ops), len(model_path)
    dp = [[(0, 0, 0) for _ in range(n + 1)] for _ in range(m + 1)]
    for i in range(1, m + 1):
        c, lm, mm = dp[i - 1][0]
        dp[i][0] = (c + 1, lm + 1, mm)
    for j in range(1, n + 1):
        c, lm, mm = dp[0][j - 1]
        dp[0][j] = (c + 1, lm, mm + 1)
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if trace_ops[i - 1] == model_path[j - 1]:
                dp[i][j] = dp[i - 1][j - 1]
            else:
                c_log, lm_log, mm_log = dp[i - 1][j]
                c_mod, lm_mod, mm_mod = dp[i][j - 1]
                if c_log + 1 <= c_mod + 1:
                    dp[i][j] = (c_log + 1, lm_log + 1, mm_log)
                else:
                    dp[i][j] = (c_mod + 1, lm_mod, mm_mod + 1)
    cost, log_moves, mod_moves = dp[m][n]
    denom = m + n if (m + n) > 0 else 1
    return 1.0 - (cost / denom), log_moves, mod_moves


def dag_alignment_fitness(
    trace_ops: Sequence[str],
    model_linearizations: Sequence[Sequence[str]],
) -> tuple[float, int, int]:
    """Adriansyah, van Dongen, & van der Aalst (EDOC 2011) conformance fitness
    minimized over valid topological linearizations sigma in L(M) of a partial order.
    """
    best: tuple[float, int, int] | None = None
    for path in model_linearizations:
        cand = linear_alignment_fitness(trace_ops, path)
        if best is None or cand[0] > best[0]:
            best = cand
    assert best is not None
    return best


def _init_blob_hash(resource: str) -> str:
    return hashlib.sha256(f"__init__:{resource}".encode("utf-8")).hexdigest()


def _edit_blob_hash(ev: TraceEvent) -> str:
    if ev.blob_state == "__init__":
        raw = f"__init__:{ev.resource}"
    elif ev.blob_state is not None:
        raw = ev.blob_state
    elif ev.patch_code:
        raw = ev.patch_code
    else:
        raw = ev.raw_args
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def compute_live_edit_slice(
    events: Sequence[TraceEvent],
    dep_cones: dict[str, set[str]],
) -> tuple[set[int], set[int]]:
    """File-granular backward causal slice over whole-resource content-hash mutations.

    Scope & boundaries:
      - Tracks SHA-256 content state per resource so revert-to-v0 cycles leave zero
        net surviving state delta at T and restore the initial cone hash.
      - Tracks diagnostic reads/searches/tests per (agent, resource) rather than
        monotone whole-agent taint, and excludes scheduler-dispatched hedge_test
        clones so unrelated-file edits or backup tests never resurrect clobbered writes.
      - Models whole-file overwrites without intra-file hunk blame or cross-file
        entrypoint call-graph dead-code pruning (documented in REPORT.md Boundaries).
    """
    cur_hash: dict[str, str] = {}
    last_writer: dict[str, int] = {}
    agent_res_deps: dict[tuple[str, str], set[int]] = collections.defaultdict(set)
    edit_parents: dict[int, set[int]] = {}

    def get_hash(r: str) -> str:
        return cur_hash.get(r, _init_blob_hash(r))

    for ev in events:
        cone = sorted(dep_cones.get(ev.resource, {ev.resource}))
        if ev.kind in {"read", "search", "test"}:  # hedge_test deliberately excluded
            for r in cone:
                if r in last_writer and get_hash(r) != _init_blob_hash(r):
                    agent_res_deps[(ev.agent, r)].add(last_writer[r])
        elif ev.kind == "edit":
            parents: set[int] = set()
            for r in cone:
                parents.update(agent_res_deps[(ev.agent, r)])
            edit_parents[ev.step] = parents
            h = _edit_blob_hash(ev)
            cur_hash[ev.resource] = h
            if h == _init_blob_hash(ev.resource):
                last_writer.pop(ev.resource, None)
            else:
                last_writer[ev.resource] = ev.step

    final_surviving = {
        step for r, step in last_writer.items() if get_hash(r) != _init_blob_hash(r)
    }
    live_edits = set(final_surviving)
    stack = sorted(final_surviving)
    while stack:
        cur = stack.pop()
        for parent in sorted(edit_parents.get(cur, set())):
            if parent not in live_edits:
                live_edits.add(parent)
                stack.append(parent)
    return final_surviving, live_edits


def decompose_trace(
    events: Sequence[TraceEvent],
    dep_cones: dict[str, set[str]],
    sibling_groups: dict[str, set[str]],
    reopen_cost_tokens: int = 2000,
) -> dict[str, Any]:
    """Decomposes a multi-agent trace into causal-epoch W_exec, W_disc, W_gen vs. naive."""
    cur_hash: dict[str, str] = {}

    def get_hash(r: str) -> str:
        return cur_hash.get(r, _init_blob_hash(r))

    def cone_resources(target: str) -> list[str]:
        return sorted(dep_cones.get(target, {target}))

    def cone_epoch(target: str) -> str:
        payload = "|".join(f"{r}:{get_hash(r)}" for r in cone_resources(target))
        return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:12]

    final_surviving_steps, live_edit_steps = compute_live_edit_slice(events, dep_cones)

    naive_seen_raw: set[tuple[str, str]] = set()
    naive_dup_steps: set[int] = set()

    seen_discovery_fleet: dict[tuple[str, str], str] = {}
    seen_discovery_agent: set[tuple[str, str, str]] = set()
    seen_test_epoch: set[tuple[str, str]] = set()

    w_exec_comp = 0
    w_exec_mut = 0
    w_disc_intra = 0
    w_disc_inter = 0
    v_verif = 0
    h_hedge = 0
    productive_base = 0
    epoch_true_waste_steps: set[int] = set()
    surviving_edits: list[TraceEvent] = []

    for ev in events:
        ep = cone_epoch(ev.resource)

        if (ev.raw_tool, ev.raw_args) in naive_seen_raw:
            naive_dup_steps.add(ev.step)
        naive_seen_raw.add((ev.raw_tool, ev.raw_args))

        if ev.kind in {"read", "search"}:
            key = (ev.resource, ep)
            if key not in seen_discovery_fleet:
                seen_discovery_fleet[key] = ev.agent
                seen_discovery_agent.add((ev.agent, ev.resource, ep))
                if any(get_hash(r) != _init_blob_hash(r) for r in cone_resources(ev.resource)):
                    v_verif += ev.tokens
                else:
                    productive_base += ev.tokens
            else:
                epoch_true_waste_steps.add(ev.step)
                if (ev.agent, ev.resource, ep) in seen_discovery_agent:
                    w_disc_intra += ev.tokens
                else:
                    w_disc_inter += ev.tokens
                seen_discovery_agent.add((ev.agent, ev.resource, ep))

        elif ev.kind == "edit":
            cur_hash[ev.resource] = _edit_blob_hash(ev)
            if ev.step not in live_edit_steps:
                w_exec_mut += ev.tokens
                epoch_true_waste_steps.add(ev.step)
            else:
                productive_base += ev.tokens
                if ev.step in final_surviving_steps:
                    surviving_edits.append(ev)

        elif ev.kind == "test":
            key = (ev.resource, ep)
            if key in seen_test_epoch:
                w_exec_comp += ev.tokens
                epoch_true_waste_steps.add(ev.step)
            else:
                seen_test_epoch.add(key)
                v_verif += ev.tokens

        elif ev.kind == "hedge_test":
            h_hedge += ev.tokens

    # Type IIIa (W_gen_bespoke): surviving edits across >=2 files with isomorphic ASTs
    skel_groups: dict[str, list[TraceEvent]] = collections.defaultdict(list)
    for ed in surviving_edits:
        if ed.patch_code:
            skel_groups[ast_skeleton(ed.patch_code)].append(ed)

    w_gen_bespoke = 0
    for _, group in sorted(skel_groups.items()):
        distinct_files = {g.resource for g in group}
        if len(distinct_files) >= 2:
            callsite_cost = int(0.15 * group[0].tokens)
            for extra in group[1:]:
                w_gen_bespoke += max(0, extra.tokens - callsite_cost)

    # Type IIIb (W_gen_omit): unfixed sibling loci in invariant equivalence classes
    touched_resources = {ed.resource for ed in surviving_edits}
    w_gen_omit = 0
    unfixed_siblings = 0
    for _, loci in sorted(sibling_groups.items()):
        fixed = loci & touched_resources
        if 0 < len(fixed) < len(loci):
            missed = len(loci) - len(fixed)
            unfixed_siblings += missed
            w_gen_omit += missed * reopen_cost_tokens

    return {
        "productive_base": productive_base,
        "v_verif": v_verif,
        "h_hedge": h_hedge,
        "w_exec_comp": w_exec_comp,
        "w_exec_mut": w_exec_mut,
        "w_disc_intra": w_disc_intra,
        "w_disc_inter": w_disc_inter,
        "w_gen_bespoke": w_gen_bespoke,
        "w_gen_omit": w_gen_omit,
        "unfixed_siblings": unfixed_siblings,
        "live_edit_steps": sorted(live_edit_steps),
        "final_surviving_edit_steps": sorted(final_surviving_steps),
        "epoch_true_waste_steps": sorted(epoch_true_waste_steps),
        "naive_raw_dup_steps": sorted(naive_dup_steps),
    }


def run_probe_1() -> dict[str, Any]:
    patch_a = """
def validate_header(hdr):
    if hdr is None or not isinstance(hdr, str):
        raise ValueError("invalid header")
    if len(hdr.strip()) == 0 or len(hdr) > 256:
        raise ValueError("bounds")
    return hdr.strip()
"""
    patch_b = """
def check_token(tok):
    if tok is None or not isinstance(tok, str):
        raise ValueError("bad token")
    if len(tok.strip()) == 0 or len(tok) > 256:
        raise ValueError("length")
    return tok.strip()
"""
    # Callee-preserving AST check: distinct callees and non-commutative arg swaps differ!
    assert ast_skeleton(patch_a) == ast_skeleton(patch_b)
    assert ast_skeleton("def f(x):\n    return foo(x)\n") != ast_skeleton("def g(y):\n    return bar(y)\n")
    assert ast_skeleton("def f(x):\n    return foo(x)\n") == ast_skeleton("def g(y):\n    return foo(y)\n")
    assert ast_skeleton("def f(x, y):\n    return x - y\n") != ast_skeleton("def g(a, b):\n    return b - a\n")

    events = [
        # Step 1: Agent A reads auth.py at initial content hash v0
        TraceEvent(1, "A", "read", "src/auth.py", "read_file", "src/auth.py", 400),
        # Steps 2-3: Agent A (grep) and Agent B (rg) search same symbol cone at v0 -> Step 3 is W_disc_inter
        TraceEvent(2, "A", "search", "sym:parse_cred", "grep", "-rn parse_cred src/", 300),
        TraceEvent(3, "B", "search", "sym:parse_cred", "rg", "parse_cred src/", 300),
        # Step 4: Agent A re-reads src/auth.py at v0 after context churn -> W_disc_intra
        TraceEvent(4, "A", "read", "src/auth.py", "read_file", "src/auth.py", 400),
        # Step 5: Agent B writes an uncoordinated conflicting edit to src/auth.py (v1) that
        #         neither Agent A nor final state ever reads/tests before overwrite -> W_exec_mut!
        TraceEvent(5, "B", "edit", "src/auth.py", "edit_file", "src/auth.py#uncoord_b", 900),
        # Step 6: Agent A writes draft edit to src/auth.py (v2), then reads (Step 7) and runs
        #         pytest (Step 8) to diagnose before writing final fix (Step 9) -> CAUSALLY LIVE!
        TraceEvent(6, "A", "edit", "src/auth.py", "edit_file", "src/auth.py#draft_a", 700),
        TraceEvent(7, "A", "read", "src/auth.py", "read_file", "src/auth.py", 400),
        TraceEvent(8, "A", "test", "test:auth", "pytest", "tests/test_auth.py", 600),
        # Step 9: Agent A refines src/auth.py (v3) informed by Step 7-8 diagnostics -> surviving
        TraceEvent(9, "A", "edit", "src/auth.py", "edit_file", "src/auth.py#final_a", 1000, patch_code=patch_a),
        # Steps 10-11: Agent A verifies src/auth.py (read + pytest) at v3 -> legitimate V_verif
        TraceEvent(10, "A", "read", "src/auth.py", "read_file", "src/auth.py", 400),
        TraceEvent(11, "A", "test", "test:auth", "pytest", "tests/test_auth.py", 600),
        # Step 12: Agent B re-runs pytest test_auth at unchanged epoch v3 -> W_exec_comp
        TraceEvent(12, "B", "test", "test:auth", "pytest", "tests/test_auth.py", 600),
        # Step 13: Authorized P95 backup test clone -> H_hedge (not W_exec)
        TraceEvent(13, "B", "hedge_test", "test:auth", "pytest_backup", "tests/test_auth.py", 600),
        # Step 14: Agent B writes isomorphic validation clone in src/session.py (W_gen_bespoke),
        #          while leaving 3rd sibling src/api_key.py unfixed (W_gen_omit)
        TraceEvent(14, "B", "edit", "src/session.py", "edit_file", "src/session.py#fix_b", 1000, patch_code=patch_b),
    ]
    dep_cones = {
        "test:auth": {"src/auth.py", "tests/test_auth.py"},
        "sym:parse_cred": {"src/auth.py", "src/session.py", "src/api_key.py"},
    }
    sibling_groups = {"cred_bounds_invariant": {"src/auth.py", "src/session.py", "src/api_key.py"}}
    res = decompose_trace(events, dep_cones, sibling_groups, reopen_cost_tokens=2000)

    assert res["live_edit_steps"] == [6, 9, 14], res
    assert res["final_surviving_edit_steps"] == [9, 14], res
    assert res["epoch_true_waste_steps"] == [3, 4, 5, 12], res
    assert res["naive_raw_dup_steps"] == [4, 7, 10, 11, 12], res
    naive_fp = set(res["naive_raw_dup_steps"]) - set(res["epoch_true_waste_steps"])
    naive_fn = set(res["epoch_true_waste_steps"]) - set(res["naive_raw_dup_steps"])
    assert naive_fp == {7, 10, 11} and naive_fn == {3, 5}
    assert res["w_disc_intra"] == 400 and res["w_disc_inter"] == 300
    assert res["w_exec_mut"] == 900 and res["w_exec_comp"] == 600
    assert res["w_gen_bespoke"] == 850 and res["w_gen_omit"] == 2000 and res["unfixed_siblings"] == 1
    assert res["v_verif"] == 2000 and res["h_hedge"] == 600

    # Soundness check A: populated sym:parse_cred cone classifies post-edit search as V_verif
    res_post_sym = decompose_trace(
        events + [TraceEvent(15, "A", "search", "sym:parse_cred", "rg", "parse_cred src/", 300)],
        dep_cones,
        sibling_groups,
    )
    assert res_post_sym["w_disc_intra"] == 400 and res_post_sym["v_verif"] == 2300

    # Soundness check B: per-(agent, resource) taint + hedge_test exclusion prevents
    # unrelated-file edits from resurrecting clobbered writes!
    isolation_events = [
        TraceEvent(1, "B", "edit", "src/auth.py", "edit_file", "src/auth.py#dead_b", 900),
        TraceEvent(2, "A", "read", "src/auth.py", "read_file", "src/auth.py", 400),
        TraceEvent(3, "A", "hedge_test", "test:auth", "pytest_backup", "tests/test_auth.py", 600),
        TraceEvent(4, "A", "edit", "docs/README.md", "edit_file", "docs/README.md#doc", 500),
        TraceEvent(5, "C", "edit", "src/auth.py", "edit_file", "src/auth.py#clean_c", 800),
    ]
    res_iso = decompose_trace(isolation_events, dep_cones, {})
    assert res_iso["live_edit_steps"] == [4, 5] and res_iso["w_exec_mut"] == 900

    # Soundness check C: SHA-256 content-hash state equivalence catches edit -> revert-to-v0 cycles!
    revert_events = [
        TraceEvent(1, "A", "read", "src/auth.py", "read_file", "src/auth.py", 400),
        TraceEvent(2, "A", "edit", "src/auth.py", "edit_file", "src/auth.py#bad", 700, blob_state="bad_v1"),
        TraceEvent(3, "A", "edit", "src/auth.py", "edit_file", "src/auth.py#revert", 300, blob_state="__init__"),
        TraceEvent(4, "A", "read", "src/auth.py", "read_file", "src/auth.py", 400),
    ]
    res_rev = decompose_trace(revert_events, dep_cones, {})
    assert res_rev["final_surviving_edit_steps"] == [] and res_rev["live_edit_steps"] == []
    assert res_rev["w_exec_mut"] == 1000 and res_rev["w_disc_intra"] == 400

    # Epoch-qualified vs epoch-blind NCD on short (< 1 KiB) traces
    iter_blind = ["read:f|edit:f|test:f" for _ in range(12)]
    iter_epoch = [f"read:f:v{k}|edit:f:v{k+1}|test:f:v{k+1}" for k in range(12)]
    dup_peer_epoch = [f"read:f:v{k}|edit:f:v{k+1}|test:f:v{k+1}" for k in range(12)]
    disjoint_peer_epoch = [f"read:g{k}:u{k}|search:q{k}:u{k}|test:t{k}:u{k}" for k in range(12)]

    ncd_blind_self = ncd_deflate(iter_blind[:6], iter_blind[6:])
    ncd_epoch_self = ncd_deflate(iter_epoch[:6], iter_epoch[6:])
    ncd_dup_agents = ncd_deflate(iter_epoch, dup_peer_epoch)
    ncd_disjoint_agents = ncd_deflate(iter_epoch, disjoint_peer_epoch)
    assert ncd_blind_self < 0.15 < ncd_epoch_self
    assert ncd_dup_agents < 0.12 and ncd_disjoint_agents > 0.55

    # Cebrian, Alfonseca, & Ortega (2005, DOI 10.4310/CIS.2005.v5.n4.a1) DEFLATE 32 KiB
    # sliding-window breakdown & finite-string metric axiom violations:
    long_trace = [
        f"step_{i:04d}|op=read_file|res=src/mod_{i:04d}.py|ep={(i * 2654435761) & 0xFFFFFFFFFFFF:012x}"
        for i in range(1200)
    ]
    long_trace_bytes = len(("\n".join(long_trace)).encode("utf-8"))
    assert long_trace_bytes == 70799 > 2 * DEFLATE_MAX_WINDOW_BYTES
    ncd_deflate_long_self = ncd_deflate(long_trace, list(long_trace))
    ncd_guarded_long_self, guard_backend = ncd_window_guarded(long_trace, list(long_trace))
    assert ncd_deflate_long_self > 1.0  # 1.0447 > 1.0 self-distance collapse!
    assert guard_backend == "lzma2_8m" and ncd_guarded_long_self < 0.015

    ncd_short_id = ncd_deflate(["read:a:v0"], ["read:a:v0"])
    ncd_sym_ab = ncd_deflate(["read:src/a.py:0001", "edit:src/b.py:9999"], ["edit:src/b.py:9999"])
    ncd_sym_ba = ncd_deflate(["edit:src/b.py:9999"], ["read:src/a.py:0001", "edit:src/b.py:9999"])
    tri_x = ["read:a:v0"] * 20
    tri_y = ["read:a:v0"] * 4
    tri_z_distinct = ["read:a:v0"] * 20 + ["read:b:v0"]
    ncd_tri_xy = ncd_deflate(tri_x, tri_y)
    ncd_tri_yz = ncd_deflate(tri_y, tri_z_distinct)
    ncd_tri_xz = ncd_deflate(tri_x, tri_z_distinct)
    assert ncd_short_id > 0.25  # 0.2727 != 0 violates identity
    assert abs(ncd_sym_ab - ncd_sym_ba) > 0.05  # 0.0625 violates symmetry
    assert ncd_tri_xz > ncd_tri_xy + ncd_tri_yz  # 0.2778 > 0.1667 violates triangle inequality

    # Alignment conformance fitness over partial-order DAG linearizations L(M)
    gold_linear_path = ["read:v0", "search:v0", "edit:v1", "read:v1", "test:v1"]
    gold_dag_linearizations = [
        ["read:v0", "search:v0", "edit:v1", "read:v1", "test:v1"],
        ["search:v0", "read:v0", "edit:v1", "read:v1", "test:v1"],
    ]
    swapped_parallel_trace = ["search:v0", "read:v0", "edit:v1", "read:v1", "test:v1"]
    churn_trace = [
        "read:v0", "read:v0", "search:v0", "search:v0",
        "edit:v0_dead", "edit:v1", "read:v1", "test:v1", "test:v1",
    ]
    fit_linear_swap, _, _ = linear_alignment_fitness(swapped_parallel_trace, gold_linear_path)
    fit_dag_swap, lm_swap, mm_swap = dag_alignment_fitness(swapped_parallel_trace, gold_dag_linearizations)
    fit_churn, lm_churn, mm_churn = dag_alignment_fitness(churn_trace, gold_dag_linearizations)
    assert abs(fit_linear_swap - 0.8) < 1e-9  # Single linear list penalizes commutative swap
    assert fit_dag_swap == 1.0 and lm_swap == 0 and mm_swap == 0  # DAG L(M) gives exact 1.0!
    assert abs(fit_churn - (1.0 - 4 / 14)) < 1e-9 and lm_churn == 4 and mm_churn == 0

    return {
        "evidence_class": EVIDENCE_EXPERIMENT,
        "live_edit_steps_backward_slice": res["live_edit_steps"],
        "dead_mutation_steps": [5],
        "isolation_check_live_steps": res_iso["live_edit_steps"],
        "revert_v0_w_exec_mut_tokens": res_rev["w_exec_mut"],
        "naive_fp_rate": round(len(naive_fp) / len(res["naive_raw_dup_steps"]), 4),
        "naive_fn_count": len(naive_fn),
        "waste_tokens": {
            "W_exec_comp": res["w_exec_comp"],
            "W_exec_mut": res["w_exec_mut"],
            "W_disc_intra": res["w_disc_intra"],
            "W_disc_inter": res["w_disc_inter"],
            "W_gen_bespoke": res["w_gen_bespoke"],
            "W_gen_omit": res["w_gen_omit"],
        },
        "ncd": {
            "blind_loop_halves": round(ncd_blind_self, 4),
            "epoch_loop_halves": round(ncd_epoch_self, 4),
            "duplicate_peers": round(ncd_dup_agents, 4),
            "disjoint_peers": round(ncd_disjoint_agents, 4),
            "deflate_70kb_identical_self": round(ncd_deflate_long_self, 4),
            "lzma2_70kb_identical_self": round(ncd_guarded_long_self, 4),
            "short_identity_violation": round(ncd_short_id, 4),
            "short_symmetry_gap": round(abs(ncd_sym_ab - ncd_sym_ba), 4),
            "short_triangle_excess": round(ncd_tri_xz - (ncd_tri_xy + ncd_tri_yz), 4),
        },
        "alignment_linear_vs_dag_parallel_swap": (round(fit_linear_swap, 4), round(fit_dag_swap, 4)),
        "alignment_churn_fitness": round(fit_churn, 4),
    }


# ============================================================================
# PROBE 2: MARBLE (8892e9cfb69282db568e6b018f2b1cd8eec31ba6) KPI/Comm Audit &
#          Collab-Overcooked (d7ae1aa5e63d8ec076e96ee437fcbbd095278ef4) Audit
# ============================================================================

def marble_paper_kpi(n_agents: int, n_milestones: int, contribs_per_agent: Sequence[int]) -> float:
    """MARBLE sections/3_method.tex L105: KPI_overall = (1 / (N * M)) * sum_j n_j."""
    return sum(contribs_per_agent) / (n_agents * n_milestones)


def marble_code_kpi_loop(iterations: Sequence[Sequence[dict[str, Any]]]) -> dict[str, Any]:
    """Exact port of MultiagentBench/MARBLE marble/evaluator/evaluator.py L160-167."""
    metrics: dict[str, Any] = {"total_milestones": 0, "agent_kpis": {}}
    for milestones in iterations:
        metrics["total_milestones"] += len(milestones)
        for milestone in milestones:
            agents = milestone.get("contributing_agents", [])
            for agent_id in agents:
                if agent_id in metrics["agent_kpis"]:
                    metrics["agent_kpis"][agent_id] += 1
                else:
                    metrics["agent_kpis"][agent_id] = 1
    return metrics


def marble_engine_and_batch_comm_avg(
    round_comms: Sequence[Sequence[str]],
    llm_rating: int = 5,
) -> tuple[list[int], float]:
    """Exact port of MARBLE engine.py L560-567 (-1 sentinel) + batch_eval.py L51-56."""
    communication_scores: list[int] = []
    for comms in round_comms:
        if comms:
            communication_scores.append(llm_rating)
        else:
            communication_scores.append(-1)  # L567 appends -1 instead of 0 from paper §3.3
    communication_avg = sum(communication_scores) / len(communication_scores)  # batch_eval.py L52
    return communication_scores, communication_avg


def collab_overcooked_eval_utils_tes(
    reference_encoded: Sequence[str],
    log_action_encoded: Sequence[str],
    beta: float = 0.95,
) -> tuple[float, float, float, int]:
    """Exact port of YusaeMeow/Collab-Overcooked src/eval_utils.py L861-895."""
    element_positions: dict[str, list[int]] = collections.defaultdict(list)
    for idx, elem in enumerate(log_action_encoded):
        element_positions[elem].append(idx)

    max_depth = 0
    starting_positions = element_positions.get(reference_encoded[0], [])
    for start_pos in starting_positions:
        pos_action = start_pos
        depth = 1
        pos_ref = 0
        while pos_ref < len(reference_encoded) - 1:
            pos_ref += 1
            ref_elem = reference_encoded[pos_ref]
            positions = element_positions.get(ref_elem, [])
            idx = bisect.bisect_right(positions, pos_action)
            if idx < len(positions):
                pos_action = positions[idx]
                depth += 1
            else:
                break
        if depth > max_depth:
            max_depth = depth

    tp = max_depth / len(reference_encoded)
    ea = 0.0 if len(log_action_encoded) == 0 else max_depth / len(log_action_encoded)
    # Eq. 1 / L893 computes F_{1/beta}(P=ea, R=tp), reversing standard F_beta polarity:
    f1 = (1.0 + beta * beta) * max_depth / (len(reference_encoded) + beta * beta * len(log_action_encoded))
    return tp, ea, f1, max_depth


def standard_f_beta_tes(m_rat: int, n_hist: int, d_max: int, beta: float) -> float:
    """Standard van Rijsbergen / ROUGE-L F_beta of precision P=D/n_hist and recall R=D/m_rat."""
    return ((1.0 + beta**2) * d_max) / ((beta**2) * m_rat + n_hist)


def collab_overcooked_l1382_guard(request_action_say: list[str]) -> bool:
    """Exact port of YusaeMeow/Collab-Overcooked src/eval_utils.py L1382 tautology."""
    return request_action_say != [] or request_action_say != ["[NONE]"]


def run_probe_2() -> dict[str, Any]:
    # 1. Paper KPI formula penalizes specialization and rewards N-way duplicate execution
    kpi_clean = marble_paper_kpi(4, 4, [1, 1, 1, 1])
    kpi_half_pileon = marble_paper_kpi(4, 4, [2, 2, 2, 2])
    kpi_full_pileon = marble_paper_kpi(4, 4, [4, 4, 4, 4])
    assert kpi_clean == 0.25 and kpi_half_pileon == 0.50 and kpi_full_pileon == 1.00

    # 2. Prompt-vs-code JSON key mismatch ("agents" vs "contributing_agents")
    prompt_obedient_state = marble_code_kpi_loop([
        [{"milestone": "M1", "agents": ["a1", "a2"]}],
        [{"milestone": "M2", "agents": ["a3", "a4"]}],
    ])
    assert prompt_obedient_state == {"total_milestones": 2, "agent_kpis": {}}

    # 3. Un-deduplicated per-iteration milestone triple-counting
    undeduplicated_state = marble_code_kpi_loop([
        [{"milestone": "M1", "contributing_agents": ["a1", "a2"]}],
        [{"milestone": "M1", "contributing_agents": ["a1", "a2"]}],
        [{"milestone": "M1", "contributing_agents": ["a1", "a2"]}],
    ])
    assert undeduplicated_state == {"total_milestones": 3, "agent_kpis": {"a1": 3, "a2": 3}}

    # 4. Silent-round -1 sentinel (engine.py L567) averaged raw by batch_eval.py L51-56
    comm_list, comm_avg = marble_engine_and_batch_comm_avg([["plan msg"], [], []], llm_rating=5)
    assert comm_list == [5, -1, -1] and round(comm_avg, 4) == 1.0

    # 5. Collab-Overcooked@d7ae1aa5e6 Eq. 1 / src/eval_utils.py L861-895 & L1382:
    ref = ["g0", "g1", "g2", "g3"]
    act_with_redundancy = ["g0", "x1", "g1", "x2", "g2", "x3", "g3", "x4"]
    _, _, tes_default_095, d_full = collab_overcooked_eval_utils_tes(ref, act_with_redundancy, beta=0.95)
    _, _, tes_b1, _ = collab_overcooked_eval_utils_tes(ref, act_with_redundancy, beta=1.0)
    _, _, tes_b2_f_inv_beta, _ = collab_overcooked_eval_utils_tes(ref, act_with_redundancy, beta=2.0)
    tes_b2_std_f2 = standard_f_beta_tes(4, 8, 4, beta=2.0)
    assert d_full == 4 and tes_b2_f_inv_beta < tes_b1 < tes_b2_std_f2

    # Greedy contiguous-prefix constraint (L862): missing g0 yields max_depth=0 despite 3/4 suffix match!
    _, _, tes_missing_g0, d_missing_g0 = collab_overcooked_eval_utils_tes(ref, ["g1", "g2", "g3"], beta=0.95)
    assert d_missing_g0 == 0 and tes_missing_g0 == 0.0

    # L1382 tautological guard evaluates True even for [] and ["[NONE]"]:
    assert collab_overcooked_l1382_guard([]) is True
    assert collab_overcooked_l1382_guard(["[NONE]"]) is True

    return {
        "evidence_class": EVIDENCE_EVALUATOR,
        "marble_kpi_clean_4x4": kpi_clean,
        "marble_kpi_half_pileon_4x4": kpi_half_pileon,
        "marble_kpi_full_pileon_4x4": kpi_full_pileon,
        "marble_prompt_schema_mismatch_agent_kpis": prompt_obedient_state["agent_kpis"],
        "marble_undeduplicated_3iter_total_milestones": undeduplicated_state["total_milestones"],
        "marble_batch_eval_comm_avg_vs_zero_rule": (round(comm_avg, 4), round(5 / 3, 4)),
        "collab_overcooked_tes_default_beta095": round(tes_default_095, 4),
        "collab_overcooked_tes_beta1": round(tes_b1, 4),
        "collab_overcooked_tes_beta2_f_inv_beta": round(tes_b2_f_inv_beta, 4),
        "collab_overcooked_tes_beta2_standard_f2": round(tes_b2_std_f2, 4),
        "collab_overcooked_missing_g0_depth": d_missing_g0,
        "collab_overcooked_l1382_tautology_empty_and_none": (
            collab_overcooked_l1382_guard([]),
            collab_overcooked_l1382_guard(["[NONE]"]),
        ),
    }


# ============================================================================
# PROBE 3: TRAIL (0ffbed9db859b4a66250dc783fa4dccf86869595),
#          MCPEval (70e1f903175a255c2967615914240f60d4d12a50),
#          & AgentBoard (bb7255e2daf1989069a186dad9e53f70680961db)
# ============================================================================

TRAIL_21_CATEGORIES = [
    "Language-only", "Tool-related", "Poor Information Retrieval", "Incorrect Memory Usage",
    "Tool Output Misinterpretation", "Incorrect Problem Identification", "Tool Selection Errors",
    "Formatting Errors", "Instruction Non-compliance", "Tool Definition Issues",
    "Environment Setup Errors", "Rate Limiting", "Authentication Errors", "Service Errors",
    "Resource Not Found", "Resource Exhaustion", "Timeout Issues", "Context Handling Failures",
    "Resource Abuse", "Goal Deviation", "Task Orchestration",
]


def trail_normalize_category(category: str, all_categories: Sequence[str]) -> str:
    """Exact port of patronus-ai/trail-benchmark benchmarking/calculate_scores.py L12-31."""
    if not category:
        return ""
    category = category.lower().strip()
    category_no_spaces = category.replace(" ", "")
    for std_cat in all_categories:
        if category == std_cat.lower() or category_no_spaces == std_cat.lower().replace(" ", ""):
            return std_cat
    for std_cat in all_categories:
        if category_no_spaces in std_cat.lower().replace(" ", ""):
            return std_cat
    return category


def trail_calculate_metrics(
    gt_errors: Sequence[dict[str, str]],
    gen_errors: Sequence[dict[str, str]],
    all_categories: Sequence[str],
) -> dict[str, Any]:
    """Exact port of patronus-ai/trail-benchmark benchmarking/calculate_scores.py L33-85."""
    gt_cats_raw = [e.get("category", "") for e in gt_errors]
    gt_locs = [e.get("location", "") for e in gt_errors]
    gen_cats_raw = [e.get("category", "") for e in gen_errors]
    gen_locs = [e.get("location", "") for e in gen_errors]

    gt_cats = [trail_normalize_category(c, all_categories) for c in gt_cats_raw if c]
    gen_cats = [trail_normalize_category(c, all_categories) for c in gen_cats_raw if c]

    gt_pairs = [(gt_locs[i], gt_cats[i]) for i in range(len(gt_locs)) if i < len(gt_cats)]
    gen_pairs = [(gen_locs[i], gen_cats[i]) for i in range(len(gen_locs)) if i < len(gen_cats)]

    common_pairs = set(gt_pairs).intersection(set(gen_pairs))
    joint_acc = len(common_pairs) / len(set(gt_pairs)) if gt_pairs else 0.0
    common_locs = set(gt_locs).intersection(set(gen_locs))
    loc_acc = len(common_locs) / len(set(gt_locs)) if gt_locs else 0.0

    y_true = [1 if cat in gt_cats else 0 for cat in all_categories]
    y_pred = [1 if cat in gen_cats else 0 for cat in all_categories]

    prec = len(common_pairs) / len(set(gen_pairs)) if gen_pairs else (1.0 if not gt_pairs else 0.0)
    rec = len(common_pairs) / len(set(gt_pairs)) if gt_pairs else (1.0 if not gen_pairs else 0.0)
    joint_f1 = (2 * prec * rec / (prec + rec)) if (prec + rec) > 0 else 0.0

    return {
        "location_accuracy": loc_acc,
        "joint_accuracy": joint_acc,
        "y_true": y_true,
        "y_pred": y_pred,
        "joint_f1_fixed": joint_f1,
    }


def mcpeval_evaluate_task(
    gt_calls: Sequence[tuple[str, dict[str, Any]]],
    pred_calls: Sequence[tuple[str, dict[str, Any]]],
    flexible: bool = False,
) -> dict[str, Any]:
    """Exact line-for-line port of SalesforceAIResearch/MCPEval static_tool_eval.py L89-440."""
    def norm_val(v: Any) -> Any:
        if isinstance(v, str):
            return v.strip().lower()
        if isinstance(v, (int, float)) and not isinstance(v, bool):
            return float(v)
        if isinstance(v, list):
            return [norm_val(x) for x in v]
        if isinstance(v, dict):
            return {norm_val(k): norm_val(val) for k, val in v.items()}
        return v

    def cmp_val(v1: Any, v2: Any) -> bool:
        nv1, nv2 = norm_val(v1), norm_val(v2)
        if isinstance(nv1, float) and isinstance(nv2, float):
            if flexible:
                if abs(nv1) < 1.0 or abs(nv2) < 1.0:
                    return abs(nv1 - nv2) < 0.2
                return abs(nv1 - nv2) / max(abs(nv1), abs(nv2)) < 0.2
            return abs(nv1 - nv2) < 1e-6
        if flexible and isinstance(nv1, str) and isinstance(nv2, str):
            if nv1.lower() in nv2.lower() or nv2.lower() in nv1.lower():
                return True
        return nv1 == nv2

    def cmp_params(gp: dict[str, Any], pp: dict[str, Any]) -> tuple[float, dict[str, tuple[Any, Any]]]:
        gt_keys, pred_keys = set(gp.keys()), set(pp.keys())
        common = gt_keys & pred_keys
        mismatched: dict[str, tuple[Any, Any]] = {}
        matched = 0
        for k in sorted(common):
            if cmp_val(gp[k], pp[k]):
                matched += 1
            else:
                mismatched[k] = (gp[k], pp[k])
        if flexible:
            important = {
                k for k in gt_keys
                if gp[k] is not None and (not isinstance(gp[k], (list, dict, str)) or len(gp[k]) > 0)
            }
            partial = 0.0
            for k in sorted(important):
                if k in common:
                    partial += 1.0 if k not in mismatched else 0.5
            return (partial / len(important) if important else 1.0), mismatched
        # Exact static_tool_eval.py L215: divides by len(gt_params), ignoring extra pred keys!
        return (matched / len(gt_keys) if gt_keys else 1.0), mismatched

    tool_count_match = len(gt_calls) == len(pred_calls)  # L286: computed & never used!
    gt_names = [n for n, _ in gt_calls]
    pred_names = [n for n, _ in pred_calls]
    extra_tools = [n for n in pred_names if n not in gt_names]  # L302-304
    name_only_matches = sum(1 for g, p in zip(gt_names, pred_names) if g == p)  # L308-311
    tool_name_score = (
        name_only_matches / len(gt_names)
        if gt_names else (1.0 if len(pred_names) == 0 else 0.0)
    )

    pos_param_scores: list[float] = []
    param_matches: dict[str, float] = {}
    exact_matches = 0
    for i, ((gn, gp), (pn, pp)) in enumerate(zip(gt_calls, pred_calls)):  # L331-362
        if gn == pn:
            pscore, _ = cmp_params(gp, pp)
            pos_param_scores.append(pscore)
            dup_name = any(j != i and gt_calls[j][0] == gn for j in range(len(gt_calls)))
            key = f"{gn}_{i}" if dup_name else gn
            param_matches[key] = pscore
            if pscore == 1.0:
                exact_matches += 1

    if pos_param_scores:
        param_match_score = sum(pos_param_scores) / len(pos_param_scores)
    elif len(gt_names) == 0 and len(pred_names) == 0:
        param_match_score = 1.0
    else:
        param_match_score = 0.0

    if len(gt_names) == 0 and len(pred_names) == 0:
        order_score = 1.0
    else:
        m, n = len(gt_names), len(pred_names)
        dp = [[0] * (n + 1) for _ in range(m + 1)]
        for i in range(1, m + 1):
            for j in range(1, n + 1):
                dp[i][j] = (
                    dp[i - 1][j - 1] + 1
                    if gt_names[i - 1] == pred_names[j - 1]
                    else max(dp[i - 1][j], dp[i][j - 1])
                )
        order_score = dp[m][n] / max(len(gt_names), 1)  # L385-386

    if flexible:
        if len(gt_calls) == 0 and len(pred_calls) == 0:
            success = True
        else:
            req_ok = all(s >= 0.6 for s in param_matches.values())
            success = (name_only_matches == len(gt_calls)) and req_ok and (order_score >= 0.5)
    else:
        if len(gt_calls) == 0 and len(pred_calls) == 0:
            success = True
        else:
            success = (exact_matches == len(gt_calls)) and (len(extra_tools) == 0) and (order_score == 1.0)

    overall = 0.4 * tool_name_score + 0.4 * param_match_score + 0.2 * order_score
    return {
        "success": success,
        "overall_score": round(overall, 4),
        "tool_count_match": tool_count_match,
        "extra_tools_len": len(extra_tools),
    }


def run_probe_3() -> dict[str, Any]:
    gt = [
        {"location": "span_07", "category": "Poor Information Retrieval"},
        {"location": "span_19", "category": "Goal Deviation"},
    ]
    spam_all = [
        {"location": f"span_{i:02d}", "category": c}
        for i in range(25) for c in TRAIL_21_CATEGORIES
    ]
    res_spam = trail_calculate_metrics(gt, spam_all, TRAIL_21_CATEGORIES)
    assert res_spam["location_accuracy"] == 1.0 and res_spam["joint_accuracy"] == 1.0
    assert abs(res_spam["joint_f1_fixed"] - (4.0 / 527.0)) < 1e-9

    # Category-preserving span-broadcast exploit (S x C_hat): identical y_pred / weighted_f1!
    base_wrong_spans = [
        {"location": "span_01", "category": "Poor Information Retrieval"},
        {"location": "span_02", "category": "Goal Deviation"},
    ]
    c_hat = ["Poor Information Retrieval", "Goal Deviation"]
    span_broadcast = [{"location": f"span_{i:02d}", "category": c} for i in range(25) for c in c_hat]
    res_base = trail_calculate_metrics(gt, base_wrong_spans, TRAIL_21_CATEGORIES)
    res_bcast = trail_calculate_metrics(gt, span_broadcast, TRAIL_21_CATEGORIES)
    assert res_base["y_pred"] == res_bcast["y_pred"]
    assert res_base["location_accuracy"] == 0.0 and res_base["joint_accuracy"] == 0.0
    assert res_bcast["location_accuracy"] == 1.0 and res_bcast["joint_accuracy"] == 1.0

    # Zero-error ground-truth trace (3 GAIA + 1 SWE-Bench in official repo) -> Oracle gets 0.0!
    res_clean_oracle = trail_calculate_metrics([], [], TRAIL_21_CATEGORIES)
    assert res_clean_oracle["location_accuracy"] == 0.0 and res_clean_oracle["joint_accuracy"] == 0.0
    gaia_oracle_ceiling = 113 / 116  # 117 files - 1 trailing-comma JSONDecodeError = 116; 3 zero-error
    sweb_oracle_ceiling = 30 / 31    # 31 files; 1 zero-error

    gen_shifted = [
        {"location": "span_01", "category": ""},
        {"location": "span_07", "category": "Poor Information Retrieval"},
        {"location": "span_19", "category": "Goal Deviation"},
    ]
    res_shift = trail_calculate_metrics(gt, gen_shifted, TRAIL_21_CATEGORIES)
    assert res_shift["location_accuracy"] == 1.0 and res_shift["joint_accuracy"] == 0.0
    assert trail_normalize_category("a", TRAIL_21_CATEGORIES) == "Language-only"

    gt_mcp = [("read_file", {"path": "src/a.py"}), ("read_file", {"path": "src/b.py"})]
    pred_50_dups = gt_mcp + [("read_file", {"path": f"garbage_{k}.py"}) for k in range(50)]
    res_mcpe_dups = mcpeval_evaluate_task(gt_mcp, pred_50_dups, flexible=False)
    assert res_mcpe_dups == {
        "success": True, "overall_score": 1.0, "tool_count_match": False, "extra_tools_len": 0,
    }

    pred_extra_kw = [
        ("read_file", {"path": "src/a.py", "bogus_param": 999}),
        ("read_file", {"path": "src/b.py", "injected_flag": True}),
    ]
    res_mcpe_extra_kw = mcpeval_evaluate_task(gt_mcp, pred_extra_kw, flexible=False)
    assert res_mcpe_extra_kw["success"] is True and res_mcpe_extra_kw["overall_score"] == 1.0

    pred_swapped = [("read_file", {"path": "src/b.py"}), ("read_file", {"path": "src/a.py"})]
    res_mcpe_swap = mcpeval_evaluate_task(gt_mcp, pred_swapped, flexible=False)
    assert res_mcpe_swap["success"] is False and res_mcpe_swap["overall_score"] == 0.6

    pred_empty_str = [("read_file", {"path": ""}), ("read_file", {"path": ""})]
    res_mcpe_empty = mcpeval_evaluate_task(gt_mcp, pred_empty_str, flexible=True)
    assert res_mcpe_empty["success"] is True and res_mcpe_empty["overall_score"] == 1.0

    high_water_pr = max([1.0, 0.0] + [0.0] * 40)
    gr_before_churn = 1.0 / 2.0
    gr_after_40_redundant_reads = (1.0 + 40.0) / 42.0
    assert high_water_pr == 1.0 and gr_before_churn == 0.5 and gr_after_40_redundant_reads > 0.97

    return {
        "evidence_class": EVIDENCE_EVALUATOR,
        "trail_spam_525_joint_acc_vs_f1": (res_spam["joint_accuracy"], round(res_spam["joint_f1_fixed"], 4)),
        "trail_span_broadcast_same_y_pred_joint_jump": (res_base["joint_accuracy"], res_bcast["joint_accuracy"]),
        "trail_oracle_ceilings_gaia_sweb": (round(gaia_oracle_ceiling, 4), round(sweb_oracle_ceiling, 4)),
        "trail_empty_cat_shift_joint_acc": res_shift["joint_accuracy"],
        "mcpeval_50_dups_strict_success": res_mcpe_dups["success"],
        "mcpeval_extra_kwarg_strict_success": res_mcpe_extra_kw["success"],
        "mcpeval_commutative_swap_strict_success": res_mcpe_swap["success"],
        "mcpeval_empty_str_flexible_score": res_mcpe_empty["overall_score"],
        "agentboard_gr_inflation": (gr_before_churn, round(gr_after_40_redundant_reads, 4)),
    }


# ============================================================================
# PROBE 4: CooperBench (63b9d44d9f docker/modal vs. gcp_batch split-brain),
#          SyncMind (a48c469fc7 & Table C1), Commit0 (1123db3321),
#          & TheAgentCompany (98b68ef82a & Table 1)
# ============================================================================

def cooperbench_test_merged_port(
    patch1_identical_patch2: bool,
    any_apply_failed: bool,
    naive_conflict: bool,
    merged_passes: tuple[bool, bool],
    agent1_applied: bool,
    agent1_solo_passes: tuple[bool, bool],
) -> dict[str, Any]:
    """Exact port of cooperbench/CooperBench src/cooperbench/eval/sandbox.py L182-298."""
    if patch1_identical_patch2:
        return {
            "status": "identical",
            "strategy": "skip-merge-identical",
            "both_passed": merged_passes[0] and merged_passes[1],
        }
    if any_apply_failed:
        merge_status = "missing_input"
    elif naive_conflict:
        merge_status = "conflicts"
    else:
        merge_status = "clean"

    if merge_status == "clean":
        return {
            "status": "clean",
            "strategy": "naive",
            "both_passed": merged_passes[0] and merged_passes[1],
        }

    # L258-270: tests ONLY agent1 (features[0] in coop / lead in team), never agent2!
    t1_pass, t2_pass = False, False
    winning_solo: str | None = None
    if agent1_applied and agent1_solo_passes[0] and agent1_solo_passes[1]:
        t1_pass, t2_pass = True, True
        winning_solo = "agent1"
    return {
        "status": merge_status,
        "strategy": "naive" if winning_solo is None else f"solo-{winning_solo}",
        "both_passed": t1_pass and t2_pass,
    }


def cooperbench_gcp_batch_port(
    runs: Sequence[dict[str, bool]],
) -> dict[str, Any]:
    """Exact port of cooperbench/CooperBench eval/backends/gcp.py L204-247 +
    eval/evaluate.py L290-299, L481 (multi-run --backend gcp / gcp_batch).
    """
    passed = 0
    failed = 0
    errors = 0
    for r in runs:
        if r["naive_clean"]:
            both = r["merged_f1"] and r["merged_f2"]
            error = None
        elif r["union_clean"]:
            both = r["union_f1"] and r["union_f2"]
            error = None
        else:
            # gcp.py L231: writes {"feature1_passed": false, "feature2_passed": false, "error": "merge_failed"}
            both = False
            error = "merge_failed"
        # evaluate.py L290-299: counts batch_result.error under errors, NOT failed!
        if error:
            errors += 1
        elif both:
            passed += 1
        else:
            failed += 1
    return {
        "passed": passed,
        "failed": failed,
        "errors": errors,
        "reported_pass_rate": passed / max(passed + failed, 1),  # evaluate.py L481
        "true_pass_rate_over_runs": passed / max(len(runs), 1),
    }


def syncmind_react_eval_port(pyfile_path: str, fm_name: str, agent_answer: str) -> int:
    """Exact port of xhguo7/SyncMind evals/react_eval.py L22-36."""
    gt_absolute_pyfile_path = "/workspace/test_repo" + pyfile_path.split("test_repo")[1]
    gold_react = f"{gt_absolute_pyfile_path}\n{fm_name}"
    react_grade = 0
    if not agent_answer:
        return react_grade
    if gold_react in agent_answer:
        react_grade = 1
    if (gt_absolute_pyfile_path in agent_answer) and (fm_name in agent_answer):
        react_grade = 1
    return react_grade


def syncmind_run_evaluation_port(entries: Sequence[dict[str, Any]]) -> tuple[dict[str, Any], Any]:
    """Exact port of xhguo7/SyncMind run_eval.py L39-57 & L125-196."""
    eval_result: dict[str, Any] = {
        k: {"SR": 0, "LA_file": 0, "LA_func": 0}
        for k in ("total", "independent", "collaborative")
    }
    for d in entries:
        mode = d["resync_method"]
        if d["adapt_grade"] == 1:
            la_func_i, la_file_i = 1, 1
        else:
            la_func_i = d["react_grade"]
            la_file_i = la_func_i
            if d["pyfile_path"].split("test_repo/")[-1] in d["agent_answer"]:
                la_file_i = 1
        eval_result["total"]["SR"] += d["adapt_grade"]
        eval_result["total"]["LA_func"] += la_func_i
        eval_result["total"]["LA_file"] += la_file_i

        eval_result[mode]["SR"] += d["adapt_grade"]
        eval_result[mode]["LA_func"] += d["react_grade"]  # L156 bug: raw react_grade!
        eval_result[mode]["LA_file"] += la_file_i

    saved_before_overwrite = json.loads(json.dumps(eval_result))
    returned_by_run_evaluation = None  # L176 & L193 overwrite self.eval_result with None
    return saved_before_overwrite, returned_by_run_evaluation


def commit0_evaluate_branch_loop_port(
    examples: Sequence[tuple[str, str]],
    branch: str | None = None,
) -> list[str]:
    """Exact port of commit-0/commit0 commit0/harness/evaluate.py L54-56."""
    resolved_branches: list[str] = []
    for _, active_branch in examples:
        if branch is None:
            branch = active_branch  # L56 mutates outer `branch`, sticking to repo #0!
        resolved_branches.append(branch)
    return resolved_branches


def spearman_rho(xs: Sequence[float], ys: Sequence[float]) -> float:
    def ranks(vals: Sequence[float]) -> list[float]:
        indexed = sorted(enumerate(vals), key=lambda t: t[1])
        out = [0.0] * len(vals)
        i = 0
        while i < len(indexed):
            j = i
            while j + 1 < len(indexed) and indexed[j + 1][1] == indexed[i][1]:
                j += 1
            avg_r = (i + j) / 2.0 + 1.0
            for k in range(i, j + 1):
                out[indexed[k][0]] = avg_r
            i = j + 1
        return out

    rx, ry = ranks(xs), ranks(ys)
    mx, my = sum(rx) / len(rx), sum(ry) / len(ry)
    num = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    den = math.sqrt(sum((a - mx) ** 2 for a in rx) * sum((b - my) ** 2 for b in ry))
    return num / den if den > 0 else 0.0


def run_probe_4() -> dict[str, Any]:
    # 4A [exact reproduction of pinned evaluator logic]: CooperBench@63b9d44d9f split-brain
    lead_dup = cooperbench_test_merged_port(False, False, True, (False, False), True, (True, True))
    member_dup = cooperbench_test_merged_port(False, False, True, (False, False), True, (True, False))
    assert lead_dup == {"status": "conflicts", "strategy": "solo-agent1", "both_passed": True}
    assert member_dup == {"status": "conflicts", "strategy": "naive", "both_passed": False}

    # On --backend gcp (len(runs) > 1), zero solo-agent1 fallback + merge_failed excluded from denominator!
    gcp_batch = cooperbench_gcp_batch_port([
        {"naive_clean": True, "merged_f1": True, "merged_f2": True, "union_clean": False, "union_f1": False, "union_f2": False},
        {"naive_clean": False, "merged_f1": False, "merged_f2": False, "union_clean": False, "union_f1": False, "union_f2": False},
        {"naive_clean": False, "merged_f1": False, "merged_f2": False, "union_clean": False, "union_f1": False, "union_f2": False},
        {"naive_clean": False, "merged_f1": False, "merged_f2": False, "union_clean": False, "union_f1": False, "union_f2": False},
    ])
    assert gcp_batch["reported_pass_rate"] == 1.0 and gcp_batch["true_pass_rate_over_runs"] == 0.25

    # 4B [exact reproduction of pinned evaluator logic]: SyncMind@a48c469fc7 & Commit0@1123db3321
    repo_dump_ans = "files: /workspace/test_repo/a/x.py /workspace/test_repo/b/y.py; symbols: foo, target_fn, bar"
    assert syncmind_react_eval_port("/host/test_repo/b/y.py", "target_fn", repo_dump_ans) == 1

    sm_saved, sm_ret = syncmind_run_evaluation_port([
        {"resync_method": "independent", "adapt_grade": 1, "react_grade": 0,
         "pyfile_path": "/workspace/test_repo/a/x.py", "agent_answer": ""},
        {"resync_method": "collaborative", "adapt_grade": 0, "react_grade": 0,
         "pyfile_path": "/workspace/test_repo/b/y.py", "agent_answer": "ls: a/x.py b/y.py c/z.py"},
    ])
    assert sm_ret is None
    assert sm_saved["total"]["LA_func"] == 1
    assert sm_saved["independent"]["LA_func"] + sm_saved["collaborative"]["LA_func"] == 0
    assert sm_saved["collaborative"]["LA_file"] == 1

    c0_branches = commit0_evaluate_branch_loop_port([("org/lib1", "agent-branch-1"), ("org/lib2", "main")], branch=None)
    assert c0_branches == ["agent-branch-1", "agent-branch-1"]

    # 4C [exact calculation on published benchmark table]: SyncMind arXiv:2502.06994v2 Table C1
    syncmind_table_c1 = [
        ("Llama-3.1-8B", 99.38, 0.33, 99.43, 1.33),
        ("Llama-3.1-70B", 98.36, 2.67, 97.92, 3.33),
        ("GPT-4o-mini", 97.98, 3.99, 97.49, 5.32),
        ("DeepSeek", 94.81, 7.33, 95.03, 7.67),
        ("GPT-4o", 97.62, 4.00, 95.79, 8.00),
        ("Llama-3.3-70B", 90.32, 16.33, 88.33, 19.00),
        ("Claude-3.5-Sonnet", 82.73, 28.18, 81.79, 33.70),
    ]
    rho_sm_ind = spearman_rho([r[1] for r in syncmind_table_c1], [r[2] for r in syncmind_table_c1])
    rho_sm_col = spearman_rho([r[3] for r in syncmind_table_c1], [r[4] for r in syncmind_table_c1])
    assert abs(rho_sm_ind - (-1.0)) < 1e-9
    assert abs(rho_sm_col - (-27.0 / 28.0)) < 1e-9

    # 4D [exact calculation on published benchmark table]: TheAgentCompany arXiv:2412.14161v3 Table 1
    tac_table1 = [
        ("Gemini-2.5-Pro", 30.3, 53, 39.3, 27.2, 4.2),
        ("Claude-3.7-Sonnet", 26.3, 46, 36.4, 27.8, 4.1),
        ("Claude-3.5-Sonnet", 24.0, 42, 34.4, 29.2, 6.3),
        ("Gemini-2.0-Flash", 11.4, 20, 19.0, 39.9, 0.6),
        ("GPT-4o", 8.6, 15, 16.7, 14.6, 1.3),
        ("Llama-3.1-405b", 7.4, 13, 14.1, 23.0, 3.2),
        ("Llama-3.3-70b", 6.9, 12, 12.8, 20.9, 0.9),
        ("Qwen-2.5-72b", 5.7, 10, 11.8, 24.0, 1.5),
        ("Gemini-1.5-Pro", 3.4, 6, 8.0, 22.1, 6.8),
        ("Amazon-Nova-Pro-v1", 1.7, 3, 5.7, 19.6, 1.6),
        ("Llama-3.1-70b", 1.7, 3, 6.5, 19.2, 0.8),
        ("Qwen-2-72b", 1.1, 2, 4.2, 23.7, 0.3),
    ]
    raw_steps = [r[4] for r in tac_table1]
    steps_per_solved_pct = [r[4] / (r[1] / 100.0) for r in tac_table1]
    steps_per_solved_exact = [r[4] / (r[2] / 175.0) for r in tac_table1]
    cost_per_solved = {r[0]: round(r[5] / (r[1] / 100.0), 2) for r in tac_table1}
    steps_per_solved_map = {r[0]: round(r[4] / (r[1] / 100.0), 1) for r in tac_table1}

    by_raw_steps = [r[0] for r in sorted(tac_table1, key=lambda r: r[4])]
    by_solved_steps = [r[0] for r in sorted(tac_table1, key=lambda r: r[4] / r[1])]
    assert by_solved_steps[:3] == ["Gemini-2.5-Pro", "Claude-3.7-Sonnet", "Claude-3.5-Sonnet"]
    assert [by_raw_steps.index(m) + 1 for m in by_solved_steps[:3]] == [9, 10, 11]
    rho_tac_pct = spearman_rho(raw_steps, steps_per_solved_pct)
    rho_tac_exact = spearman_rho(raw_steps, steps_per_solved_exact)
    assert abs(rho_tac_pct - (-5.0 / 13.0)) < 1e-9
    assert abs(rho_tac_exact - (-5.0 / 13.0)) < 1e-9

    return {
        "evidence_classes": {
            "cooperbench_syncmind_commit0_code": EVIDENCE_EVALUATOR,
            "syncmind_table_c1_and_tac_table1": EVIDENCE_TABLE,
        },
        "cooperbench_docker_lead_vs_member_dup_passed": (lead_dup["both_passed"], member_dup["both_passed"]),
        "cooperbench_gcp_batch_reported_vs_true_pass_rate": (
            gcp_batch["reported_pass_rate"], gcp_batch["true_pass_rate_over_runs"],
        ),
        "syncmind_la_func_partition_gap": (
            sm_saved["total"]["LA_func"]
            - (sm_saved["independent"]["LA_func"] + sm_saved["collaborative"]["LA_func"])
        ),
        "syncmind_react_eval_repo_dump_grade": 1,
        "commit0_branch_none_loop_sticky_bug": c0_branches,
        "syncmind_eff_time_vs_sr_spearman_ind_collab": (round(rho_sm_ind, 4), round(rho_sm_col, 4)),
        "tac_gpt4o_vs_gemini25_steps_per_solved": (
            steps_per_solved_map["GPT-4o"], steps_per_solved_map["Gemini-2.5-Pro"],
        ),
        "tac_gpt4o_vs_gemini25_cost_per_solved": (
            cost_per_solved["GPT-4o"], cost_per_solved["Gemini-2.5-Pro"],
        ),
        "tac_top3_raw_step_ranks": [9, 10, 11],
        "tac_raw_vs_solved_steps_spearman": round(rho_tac_pct, 4),
    }


# ============================================================================
# PROBE 5: Stratified Simpson's Paradox vs. Renewal CPS & Common-Support Ratio
#          + All 20 Verbatim Models on MCP-Bench (arXiv:2508.20453v1)
# ============================================================================

def run_probe_5() -> dict[str, Any]:
    weak_pass_costs = [0.80] * 18 + [2.00] * 2
    weak_fail_costs = [0.80] * 2 + [1.40] * 38 + [1.60] * 40
    strong_pass_costs = [0.60] * 20 + [1.50] * 30 + [4.80] * 15
    strong_fail_costs = [1.05] * 10 + [2.40] * 25

    cond_weak = sum(weak_pass_costs) / len(weak_pass_costs)
    cond_strong = sum(strong_pass_costs) / len(strong_pass_costs)
    uncond_weak = (sum(weak_pass_costs) + sum(weak_fail_costs)) / 100.0
    uncond_strong = (sum(strong_pass_costs) + sum(strong_fail_costs)) / 100.0
    cps_weak = (sum(weak_pass_costs) + sum(weak_fail_costs)) / len(weak_pass_costs)
    cps_strong = (sum(strong_pass_costs) + sum(strong_fail_costs)) / len(strong_pass_costs)
    paired_ratio = (18 * 0.60 + 2 * 1.50) / (18 * 0.80 + 2 * 2.00)

    assert cond_weak < cond_strong and uncond_weak < uncond_strong
    assert cps_strong < cps_weak and abs(paired_ratio - 0.75) < 1e-9

    mcp_bench_20 = [
        ("llama-3-1-8b-instruct", 0.428, 17.3, 155.6, 0.141),
        ("llama-3-2-90b-vision-instruct", 0.495, 11.8, 55.9, 0.173),
        ("nova-micro-v1", 0.508, 10.8, 58.1, 0.212),
        ("llama-3-1-70b-instruct", 0.510, 12.3, 63.0, 0.191),
        ("mistral-small-2503", 0.530, 6.5, 67.0, 0.232),
        ("gpt-4o-mini", 0.557, 14.2, 60.6, 0.201),
        ("llama-3-3-70b-instruct", 0.558, 5.8, 26.9, 0.262),
        ("gemma-3-27b-it", 0.582, 7.8, 42.3, 0.249),
        ("gpt-4o", 0.595, 5.8, 21.8, 0.272),
        ("gemini-2.5-flash-lite", 0.598, 11.4, 86.8, 0.226),
        ("qwen3-30b-a3b-instruct-2507", 0.627, 4.0, 24.1, 0.303),
        ("kimi-k2", 0.629, 3.9, 20.6, 0.307),
        ("gpt-oss-20b", 0.654, 4.4, 31.7, 0.309),
        ("glm-4.5", 0.668, 8.7, 42.9, 0.297),
        ("qwen3-235b-a22b-2507", 0.678, 4.0, 16.4, 0.355),
        ("claude-sonnet-4", 0.681, 9.2, 44.2, 0.328),
        ("gemini-2.5-pro", 0.690, 8.2, 37.4, 0.329),
        ("gpt-oss-120b", 0.692, 7.0, 43.0, 0.329),
        ("o3", 0.715, 6.3, 28.3, 0.359),
        ("gpt-5", 0.749, 9.2, 78.9, 0.339),
    ]
    assert len(mcp_bench_20) == 20
    gpt5_width = 78.9 / 9.2
    o3_width = 28.3 / 6.3
    assert round(gpt5_width, 2) == 8.58 and round(o3_width, 2) == 4.49

    rho_calls_vs_score = spearman_rho([m[3] for m in mcp_bench_20], [m[1] for m in mcp_bench_20])
    rho_rounds_vs_score = spearman_rho([m[2] for m in mcp_bench_20], [m[1] for m in mcp_bench_20])
    rho_pareff_vs_score = spearman_rho([m[4] for m in mcp_bench_20], [m[1] for m in mcp_bench_20])
    assert rho_pareff_vs_score > 0.90

    return {
        "evidence_classes": {
            "simpson_stratified_mixture": EVIDENCE_EXPERIMENT,
            "mcp_bench_20_models": EVIDENCE_TABLE,
        },
        "simpson_cond_pass_weak_vs_strong": (round(cond_weak, 4), round(cond_strong, 4)),
        "uncond_cost_weak_vs_strong": (round(uncond_weak, 4), round(uncond_strong, 4)),
        "cps_weak_vs_strong": (round(cps_weak, 4), round(cps_strong, 4)),
        "common_support_paired_ratio": round(paired_ratio, 4),
        "mcp_bench_20_gpt5_vs_o3_parallel_width": (round(gpt5_width, 2), round(o3_width, 2)),
        "mcp_bench_20_spearman_calls_vs_score": round(rho_calls_vs_score, 4),
        "mcp_bench_20_spearman_rounds_vs_score": round(rho_rounds_vs_score, 4),
        "mcp_bench_20_spearman_pareff_vs_score": round(rho_pareff_vs_score, 4),
    }


def main() -> None:
    banners = [
        f"Probe 1: {EVIDENCE_EXPERIMENT} Causal-epoch (W_exec, W_disc, W_gen) + SHA-256 slice + DEFLATE/LZMA2 NCD + DAG alignment",
        f"Probe 2: {EVIDENCE_EVALUATOR} MARBLE@8892e9cfb6 KPI/comm/batch_eval + Collab-Overcooked@d7ae1aa5e6 F_{{1/beta}}/prefix/L1382",
        f"Probe 3: {EVIDENCE_EVALUATOR} TRAIL@0ffbed9db8 + MCPEval@70e1f90317 + AgentBoard@bb7255e2da evaluator audits",
        f"Probe 4: {EVIDENCE_EVALUATOR} + {EVIDENCE_TABLE} CooperBench@63b9d44d9f (docker+gcp) + SyncMind@a48c469fc7 + Commit0 + TAC",
        f"Probe 5: {EVIDENCE_EXPERIMENT} + {EVIDENCE_TABLE} Stratified Simpson's paradox vs CPS/paired ratio + MCP-Bench 20 models",
    ]
    for b in banners:
        print(b)

    results = {
        "probe_1": run_probe_1(),
        "probe_2": run_probe_2(),
        "probe_3": run_probe_3(),
        "probe_4": run_probe_4(),
        "probe_5": run_probe_5(),
    }
    payload = json.dumps(results, indent=2, sort_keys=True)
    digest = hashlib.sha256(payload.encode("utf-8")).hexdigest()
    print(f"ALL 5 PROBES PASSED DETERMINISTICALLY (json_sha256={digest[:16]})")
    print(payload)


if __name__ == "__main__":
    main()
