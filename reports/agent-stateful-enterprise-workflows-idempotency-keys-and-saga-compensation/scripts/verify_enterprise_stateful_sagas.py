#!/usr/bin/env python3
"""Deterministic verification suite for long-horizon stateful enterprise tool-use,
evaluator side-effect blind spots, HTTP idempotency keys, saga compensation,
aligned context-environment rewind, and compositional horizon scaling.

Pure Python 3.10+ standard library only. Deterministic across PYTHONHASHSEED.
"""

from __future__ import annotations

from collections import OrderedDict, defaultdict
from dataclasses import dataclass, field
import hashlib
import heapq
import itertools
import json
import math
import sys
from typing import Any, Callable


# =============================================================================
# PROBE 1: Stateful Benchmark Evaluator Blind-Spot & Repair Reproductions
# =============================================================================


# --- 1A. StonyBrookNLP/appworld@42b5bcf3cd334fee33f0c37c02070a9f5807add5 ---
# Faithful port of:
#   - src/appworld/apps/lib/models/orm.py:1074-1087 (SQLModel.set_record_hash)
#   - src/appworld/collections/models.py:104-130 (ids_record_hashes, ids, record_hashes)
#   - src/appworld/collections/models.py:364-526 (_changed_model_names, _changed_records)


@dataclass(frozen=True)
class AppWorldRow:
    id: int
    fields: dict[str, Any]
    record_hash: str = field(init=False)

    def __post_init__(self) -> None:
        # orm.py:1075-1087: skips ("_db_home_path", "record_hash", "id"), sorts keys.
        payload = json.dumps(self.fields, sort_keys=True, separators=(",", ":")).encode("utf-8")
        digest = hashlib.blake2b(payload, digest_size=8).hexdigest()
        object.__setattr__(self, "record_hash", digest)


class AppWorldSnapshot:
    def __init__(self, tables: dict[str, list[AppWorldRow]], touched_tables: set[str]) -> None:
        self.tables = {k: list(v) for k, v in tables.items()}
        self.model_hashes = {k: (1 if k in touched_tables else 0) for k in tables}

    def size(self, model_name: str) -> int:
        return len(self.tables[model_name])

    def ids_record_hashes(self, model_name: str) -> list[tuple[int, str]]:
        # models.py:104-110
        return [(r.id, r.record_hash) for r in self.tables[model_name]]

    def ids(self, model_name: str) -> set[int]:
        # models.py:112-120
        return {ih[0] for ih in self.ids_record_hashes(model_name)}

    def record_hashes(self, model_name: str) -> set[str]:
        # models.py:122-130 (deduplicated set[str] without primary-key id)
        return {ih[1] for ih in self.ids_record_hashes(model_name)}

    def by_ids(self, model_name: str, target_ids: set[int] | list[int]) -> list[AppWorldRow]:
        wanted = set(target_ids)
        return [r for r in self.tables[model_name] if r.id in wanted]


class PinnedAppWorldDiff:
    """Exact algorithmic port of ModelCollectionPair (models.py:364-526)."""

    GLOBAL_IGNORED = ("supervisor.Task", "admin.PaymentCard", "amazon.BrowsedProduct")

    def __init__(self, start: AppWorldSnapshot, end: AppWorldSnapshot) -> None:
        self.start = start
        self.end = end

    def changed_model_names(
        self,
        include: list[str] | None = None,
        ignore: list[str] | None = None,
    ) -> set[str]:
        include_names = list(include or [])
        ignore_names = list(ignore or [])
        # models.py:376-385
        for ignored in self.GLOBAL_IGNORED:
            if ignored not in ignore_names:
                ignore_names.append(ignored)

        all_names = list(self.start.tables.keys())
        if include_names:
            candidates = list(include_names)
        else:
            candidates = [m for m in all_names if m not in ignore_names]

        # models.py:432-436: table-counter fast skip
        candidates = [
            m for m in candidates if self.start.model_hashes[m] != self.end.model_hashes[m]
        ]

        changed: set[str] = set()
        for m in candidates:
            # models.py:441-449
            if self.start.size(m) != self.end.size(m):
                changed.add(m)
                continue
            if set(self.start.record_hashes(m)) != set(self.end.record_hashes(m)):
                changed.add(m)
        return changed

    def changed_records(
        self, model_name: str, updated_state: str = "end"
    ) -> tuple[list[AppWorldRow], list[AppWorldRow], list[AppWorldRow]]:
        # models.py:487-526
        start_ids = self.start.ids(model_name)
        end_ids = self.end.ids(model_name)
        added_records = self.end.by_ids(model_name, end_ids - start_ids)
        removed_records = self.start.by_ids(model_name, start_ids - end_ids)
        if updated_state == "end":
            ids_hashes_1 = self.end.ids_record_hashes(model_name)
            ids_2 = self.start.ids(model_name)
            record_hashes_2 = self.start.record_hashes(model_name)
            source = self.end
        else:
            ids_hashes_1 = self.start.ids_record_hashes(model_name)
            ids_2 = self.end.ids(model_name)
            record_hashes_2 = self.end.record_hashes(model_name)
            source = self.start

        # models.py:501-505: compares against entire table's record_hashes_2 set
        updated_ids = [
            id_hash[0]
            for id_hash in ids_hashes_1
            if (id_hash[1] not in record_hashes_2) and (id_hash[0] in ids_2)
        ]
        updated_records = source.by_ids(model_name, updated_ids)

        # models.py:509-525: cancel added and removed records with matching record_hash
        hash_to_added: dict[str, list[AppWorldRow]] = defaultdict(list)
        for r in added_records:
            hash_to_added[r.record_hash].append(r)
        hash_to_removed: dict[str, list[AppWorldRow]] = defaultdict(list)
        for r in removed_records:
            hash_to_removed[r.record_hash].append(r)

        final_added: list[AppWorldRow] = []
        final_removed: list[AppWorldRow] = []
        for rh in sorted(hash_to_added.keys() | hash_to_removed.keys()):
            a_list = hash_to_added[rh]
            r_list = hash_to_removed[rh]
            cut = min(len(a_list), len(r_list))
            final_added.extend(a_list[cut:])
            final_removed.extend(r_list[cut:])
        final_added.sort(key=lambda r: r.id)
        final_removed.sort(key=lambda r: r.id)
        updated_records.sort(key=lambda r: r.id)
        return final_added, updated_records, final_removed


class RepairedAppWorldDiff:
    """Appendix-D-faithful primary-key + multiset relational state diff."""

    SYSTEM_ONLY_IGNORED = ("supervisor.Task",)

    def __init__(self, start: AppWorldSnapshot, end: AppWorldSnapshot) -> None:
        self.start = start
        self.end = end

    def changed_model_names(self, allow_id_rebind_tables: set[str] | None = None) -> set[str]:
        rebind = allow_id_rebind_tables or set()
        changed: set[str] = set()
        for m in self.start.tables:
            if m in self.SYSTEM_ONLY_IGNORED:
                continue
            a, u, r = self.changed_records(m, cancel_rebound_ids=(m in rebind))
            if a or u or r:
                changed.add(m)
        return changed

    def changed_records(
        self, model_name: str, cancel_rebound_ids: bool = False
    ) -> tuple[list[AppWorldRow], list[AppWorldRow], list[AppWorldRow]]:
        start_map = dict(self.start.ids_record_hashes(model_name))
        end_map = dict(self.end.ids_record_hashes(model_name))
        start_ids = set(start_map.keys())
        end_ids = set(end_map.keys())
        added = self.end.by_ids(model_name, end_ids - start_ids)
        removed = self.start.by_ids(model_name, start_ids - end_ids)
        updated_ids = [
            rid for rid in sorted(start_ids & end_ids) if start_map[rid] != end_map[rid]
        ]
        updated = self.end.by_ids(model_name, updated_ids)
        if cancel_rebound_ids:
            h_add: dict[str, list[AppWorldRow]] = defaultdict(list)
            h_rem: dict[str, list[AppWorldRow]] = defaultdict(list)
            for rec in added:
                h_add[rec.record_hash].append(rec)
            for rec in removed:
                h_rem[rec.record_hash].append(rec)
            added, removed = [], []
            for rh in sorted(h_add.keys() | h_rem.keys()):
                cut = min(len(h_add[rh]), len(h_rem[rh]))
                added.extend(h_add[rh][cut:])
                removed.extend(h_rem[rh][cut:])
        return (
            sorted(added, key=lambda r: r.id),
            sorted(updated, key=lambda r: r.id),
            sorted(removed, key=lambda r: r.id),
        )


# --- 1B. apple/ToolSandbox@c8571d7854316d2e1c5f288e59fe1e34e53f6dd1 ---
# Faithful port of:
#   - tool_sandbox/common/evaluation.py:283-344, 649-699 (snapshot_similarity & column defaults)
#   - tool_sandbox/common/evaluation.py:625-646 (guardrail_similarity)
#   - tool_sandbox/common/evaluation.py:852-915 (CachedSimilarityCalculator.calculate_similarity)
#   - tool_sandbox/common/evaluation.py:980-1163 (EvaluationResult, MilestoneMatcher._dfs)


def hungarian_min_cost(cost: list[list[float]]) -> float:
    """Exact O(n^3) Kuhn-Munkres min-cost assignment; raises ValueError when no finite
    matching exists, matching scipy.optimize.linear_sum_assignment (evaluation.py:338-341)."""
    n = len(cost)
    if n == 0:
        return 0.0
    finite_vals = [abs(v) for row in cost for v in row if not math.isinf(v) and not math.isnan(v)]
    for row in cost:
        for val in row:
            if math.isnan(val):
                raise ValueError("cost matrix contains NaN")
    inf_penalty = (sum(finite_vals) + 1.0) * (n + 2)
    work = [
        [inf_penalty if math.isinf(val) else val for val in row]
        for row in cost
    ]
    u = [0.0] * (n + 1)
    v = [0.0] * (n + 1)
    p = [0] * (n + 1)
    way = [0] * (n + 1)
    for i in range(1, n + 1):
        p[0] = i
        j0 = 0
        minv = [math.inf] * (n + 1)
        used = [False] * (n + 1)
        while True:
            used[j0] = True
            i0 = p[j0]
            delta = math.inf
            j1 = 0
            for j in range(1, n + 1):
                if not used[j]:
                    cur = work[i0 - 1][j - 1] - u[i0] - v[j]
                    if cur < minv[j]:
                        minv[j] = cur
                        way[j] = j0
                    if minv[j] < delta:
                        delta = minv[j]
                        j1 = j
            for j in range(n + 1):
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
    assigned_costs: list[float] = []
    for j in range(1, n + 1):
        orig = cost[p[j] - 1][j - 1]
        if math.isinf(orig):
            raise ValueError("cost matrix is infeasible")
        assigned_costs.append(orig)
    return sum(assigned_costs) / n


def pinned_toolsandbox_snapshot_similarity(
    snapshot: list[dict[str, Any]],
    target: list[dict[str, Any]],
) -> float:
    """Exact port of evaluation.py:283-344 over exact-match structured columns.

    Per evaluation.py:649-699, structured state columns (ids, booleans, phone numbers,
    coordinates, timestamps) use column_exact_match_similarity (0.0/1.0), whereas free-text
    'content' and 'relationship' columns default to column_rouge_l_similarity. Whenever every
    row assignment encounters at least one 0.0-similarity cell (any mismatched exact-match
    column or zero-token-overlap ROUGE-L cell), -log(0) = +inf makes linear_sum_assignment
    infeasible (ValueError -> 0.0).
    """
    if len(snapshot) != len(target):
        return 0.0
    if not target:
        return 1.0
    snap_cols = set(snapshot[0].keys()) if snapshot else set()
    targ_cols = set(target[0].keys())
    # evaluation.py:312: set(target_dataframe.columns) - set(snapshot.columns)
    if targ_cols - snap_cols:
        return 0.0
    cols = list(target[0].keys())
    cost_matrix: list[list[float]] = []
    for trow in target:
        row_costs: list[float] = []
        for srow in snapshot:
            neg_logs: list[float] = []
            for c in cols:
                sim = 1.0 if srow[c] == trow[c] else 0.0
                # evaluation.py:325: -pl.col("similarity").log()
                neg_logs.append(math.inf if sim == 0.0 else -math.log(sim))
            row_costs.append(sum(neg_logs) / len(neg_logs))
        cost_matrix.append(row_costs)
    try:
        mean_neg_log = hungarian_min_cost(cost_matrix)
    except ValueError:
        return 0.0
    return float(math.exp(-mean_neg_log))


@dataclass
class TSMilestone:
    target_db: str
    target_rows: list[dict[str, Any]]
    guardrail_dbs: list[str] = field(default_factory=list)


def run_toolsandbox_matcher(
    trajectory: list[dict[str, list[dict[str, Any]]]],
    milestones: list[TSMilestone],
    edges: list[tuple[int, int]],
    *,
    fix_pruning: bool = False,
    enforce_terminal_guardrail: bool = False,
) -> tuple[float, int]:
    """Exact port of CachedSimilarityCalculator.calculate_similarity (L852-915) and
    MilestoneMatcher._add_guardrail_constraints & _dfs (L996-1163).
    Returns (mean_similarity, dfs_expansions)."""
    num_m = len(milestones)
    preds: dict[int, set[int]] = {i: set() for i in range(num_m)}
    succs: dict[int, set[int]] = {i: set() for i in range(num_m)}
    for u, v in edges:
        preds[v].add(u)
        succs[u].add(v)

    # evaluation.py:996-1041: guardrail constraints bind milestone i only to preds[i]
    guardrail_pairs: dict[int, list[tuple[int, str]]] = {i: [] for i in range(num_m)}
    for i in range(num_m):
        g_set = set(milestones[i].guardrail_dbs)
        for j in {i} | preds[i]:
            g_set.discard(milestones[j].target_db)
        for ref_idx, db_ns in itertools.product(sorted(preds[i]), sorted(g_set)):
            guardrail_pairs[i].append((ref_idx, db_ns))

    def node_sim(m_idx: int, snap_idx: int, assigned: OrderedDict[int, tuple[int, float]]) -> float:
        # evaluation.py:863-915: multiply all constraint scores; exclude 0/1 guardrail
        # constraints from similarity_count before taking pow(similarity, 1 / similarity_count).
        ms = milestones[m_idx]
        similarity = pinned_toolsandbox_snapshot_similarity(
            trajectory[snap_idx][ms.target_db], ms.target_rows
        )
        similarity_count = 1
        for ref_idx, db_ns in guardrail_pairs[m_idx]:
            ref_snap_idx = assigned[ref_idx][0]
            guardrail_ok = (
                1.0 if trajectory[snap_idx][db_ns] == trajectory[ref_snap_idx][db_ns] else 0.0
            )
            similarity *= guardrail_ok
        return float(math.pow(similarity, 1.0 / similarity_count))

    expansions = 0
    max_snap = len(trajectory) - 1

    def dfs(
        assigned: OrderedDict[int, tuple[int, float]],
        assigned_sum: float,
        remaining: set[int],
        current_best_sum: float,
    ) -> tuple[OrderedDict[int, tuple[int, float]], float]:
        nonlocal expansions
        expansions += 1
        if not remaining:
            return assigned, assigned_sum
        last_snap = assigned[next(reversed(assigned))][0] if assigned else 0
        best_map: OrderedDict[int, tuple[int, float]] = OrderedDict()
        best_sum: float = -1.0
        heap: list[tuple[float, int, int]] = []
        for m_idx in sorted(remaining):
            if preds[m_idx] & remaining:
                continue
            for s_idx in reversed(range(last_snap, max_snap + 1)):
                sim = node_sim(m_idx, s_idx, assigned)
                heapq.heappush(heap, (-sim, m_idx, s_idx))
        while heap:
            neg_sim, m_idx, s_idx = heapq.heappop(heap)
            sim = -neg_sim
            # evaluation.py:1133-1139: compares against local best_sum instead of
            # max(current_best_sum, best_sum)
            bound = max(current_best_sum, best_sum) if fix_pruning else best_sum
            if assigned_sum + sim + len(remaining) - 1 <= bound:
                continue
            nxt_map = OrderedDict(assigned)
            nxt_map[m_idx] = (s_idx, sim)
            nxt_rem = set(remaining)
            nxt_rem.remove(m_idx)
            cand_map, cand_sum = dfs(
                nxt_map,
                assigned_sum + sim,
                nxt_rem,
                max(current_best_sum, best_sum),
            )
            if cand_sum > best_sum:
                best_map = cand_map
                best_sum = cand_sum
        return best_map, best_sum

    mapping, sim_sum = dfs(OrderedDict(), 0.0, set(range(num_m)), 0.0)
    mean_sim = sim_sum / num_m
    if enforce_terminal_guardrail and mapping:
        _, (last_snap, _) = next(reversed(mapping.items()))
        for db_ns in trajectory[max_snap]:
            if trajectory[max_snap][db_ns] != trajectory[last_snap][db_ns]:
                mean_sim = 0.0
                break
    return mean_sim, expansions


# --- 1C. ServiceNow/WorkArena@e885130962f61fb64ac305497996a46cfc7d18f0 ---
# Faithful port of:
#   - src/browsergym/workarena/tasks/compositional/base.py:217-264 (CompositionalTask.validate)
#   - src/browsergym/workarena/tasks/compositional/base.py:329-360 (InfeasibleCompositionalTask.validate)
# Note: Every InfeasibleCompositionalTask hierarchy in ServiceNow/WorkArena@e8851309
# (dash_do_base.py, dash_do_catalog_infeasible.py, dash_do_create_incident_infeasible.py,
# dash_do_create_problem_infeasible.py, dash_do_request_item_infeasible.py,
# navigate_and_do_infeasible.py) sets is_validated=False on all subtasks.


@dataclass
class WASubtask:
    name: str
    is_validated: bool
    predicate: Callable[[dict[str, Any]], bool]


class PinnedWorkArenaCompositional:
    def __init__(self, subtasks: list[WASubtask]) -> None:
        self.subtasks = subtasks
        self.valid_index = 0

    def validate(self, db_state: dict[str, Any], chat: list[dict[str, str]]) -> tuple[float, bool]:
        # base.py:221-225
        while self.valid_index < len(self.subtasks) and not self.subtasks[self.valid_index].is_validated:
            self.valid_index += 1
        if self.valid_index == len(self.subtasks):
            return 1.0, True
        # base.py:235-248: checks ONLY subtasks[valid_index] and latches valid_index += 1
        if self.subtasks[self.valid_index].predicate(db_state):
            self.valid_index += 1
        if self.valid_index == len(self.subtasks):
            return 1.0, True
        return 0.0, False


class PinnedWorkArenaInfeasible(PinnedWorkArenaCompositional):
    def __init__(self, subtasks: list[WASubtask], infeasible_reasons: list[str]) -> None:
        super().__init__(subtasks)
        self.infeasible_reasons = infeasible_reasons
        self.infeasible_reason_found = False

    def validate(self, db_state: dict[str, Any], chat: list[dict[str, str]]) -> tuple[float, bool]:
        # base.py:331-360
        if chat and chat[-1]["role"] == "infeasible":
            answer = chat[-1]["message"].lower()
        else:
            return 0.0, False
        if not self.infeasible_reason_found:
            for r in self.infeasible_reasons:
                if r.lower() in answer:
                    self.infeasible_reason_found = True
                    break
            if not self.infeasible_reason_found:
                return 0.0, False
        return super().validate(db_state, chat)


# --- 1D. TheAgentCompany/TheAgentCompany@98b68ef82a47690c316f42fddb05baafaab56851 ---
# Faithful port of:
#   - workspaces/base_image/scoring.py:5-85 (Checkpoint, Result, bonus_for_completing_final)
#   - evaluation/summarise_results.py:162-191 (calculate_score, is_perfect_completion)
#   - workspaces/tasks/finance-apply-tax-credit/evaluator.py:10-62 (17 fields / 16)


@dataclass
class TACCheckpoint:
    total: int
    result: int


def tac_bonus_for_completing_final(checkpoints: list[TACCheckpoint]) -> dict[str, int]:
    total = sum(cp.total for cp in checkpoints)
    if checkpoints and checkpoints[-1].result == checkpoints[-1].total:
        result = total
    else:
        result = sum(cp.result for cp in checkpoints)
    return {"total": total, "result": result}


def tac_metrics(total: int, result: int) -> tuple[float, float]:
    s_full = 1.0 if (total > 0 and total == result) else 0.0
    s_partial = (result / total * 0.5) + ((result // total) * 0.5)
    return s_full, s_partial


def tac_form6765_pinned_checkpoint1(matched_fields_out_of_17: int) -> int:
    # finance-apply-tax-credit/evaluator.py:59-62 (len(target_values) == 17, divides by 16)
    score = matched_fields_out_of_17
    if score == 16:
        return 5
    return round((score / 16) * 5)


def run_probe_1() -> dict[str, Any]:
    # 1A: AppWorld tests
    base_tables = {
        "venmo.Transaction": [
            AppWorldRow(1, {"sender": "alice", "amount": 50}),
            AppWorldRow(2, {"sender": "bob", "amount": 500}),
        ],
        "gmail.Email": [
            AppWorldRow(1, {"subject": "ok", "body": "clean"}),
            AppWorldRow(2, {"subject": "ok", "body": "clean"}),
            AppWorldRow(3, {"subject": "wire", "body": "send_999"}),
        ],
        "admin.PaymentCard": [
            AppWorldRow(1, {"holder": "supervisor", "limit": 1000}),
        ],
        "spotify.SongLike": [
            AppWorldRow(5, {"user_id": 1, "song_id": 42}),
        ],
    }
    mutated_tables = {
        # Case 1: 2-row swap (id=1 <-> id=2)
        "venmo.Transaction": [
            AppWorldRow(1, {"sender": "bob", "amount": 500}),
            AppWorldRow(2, {"sender": "alice", "amount": 50}),
        ],
        # Case 2: Multiplicity shift ({clean, clean, wire} -> {clean, wire, wire}) + cross-row overwrite
        "gmail.Email": [
            AppWorldRow(1, {"subject": "ok", "body": "clean"}),
            AppWorldRow(2, {"subject": "wire", "body": "send_999"}),
            AppWorldRow(3, {"subject": "wire", "body": "send_999"}),
        ],
        # Case 3: Globally ignored admin.PaymentCard tampering
        "admin.PaymentCard": [
            AppWorldRow(1, {"holder": "attacker", "limit": 99999}),
        ],
        # Case 4: Delete id=5 + re-insert id=99 with identical non-id fields
        "spotify.SongLike": [
            AppWorldRow(99, {"user_id": 1, "song_id": 42}),
        ],
    }
    snap_start = AppWorldSnapshot(base_tables, set())
    snap_end = AppWorldSnapshot(mutated_tables, set(mutated_tables.keys()))

    pinned_aw = PinnedAppWorldDiff(snap_start, snap_end)
    repaired_aw = RepairedAppWorldDiff(snap_start, snap_end)

    aw_pinned_changed = pinned_aw.changed_model_names()
    aw_pinned_swap_recs = pinned_aw.changed_records("venmo.Transaction")
    aw_pinned_mult_recs = pinned_aw.changed_records("gmail.Email")
    aw_repaired_changed = repaired_aw.changed_model_names(
        allow_id_rebind_tables={"spotify.SongLike"}
    )
    aw_repaired_strict_pk = repaired_aw.changed_model_names(allow_id_rebind_tables=set())

    assert aw_pinned_changed == set(), f"Expected blind set(), got {aw_pinned_changed}"
    assert aw_pinned_swap_recs == ([], [], [])
    assert aw_pinned_mult_recs == ([], [], [])
    assert aw_repaired_changed == {
        "venmo.Transaction",
        "gmail.Email",
        "admin.PaymentCard",
    }
    assert "spotify.SongLike" in aw_repaired_strict_pk
    assert len(repaired_aw.changed_records("venmo.Transaction")[1]) == 2
    assert [r.id for r in repaired_aw.changed_records("gmail.Email")[1]] == [2]

    # Isolated cross-row hash-shadowing test (models.py:501-505): even when table IS flagged
    # (via id=3 new value), id=1 overwritten to match untouched id=2 is silently omitted from
    # pinned changed_records()[1].
    shadow_start = AppWorldSnapshot(
        {
            "venmo.Request": [
                AppWorldRow(1, {"status": "pending"}),
                AppWorldRow(2, {"status": "approved"}),
                AppWorldRow(3, {"status": "pending"}),
            ]
        },
        set(),
    )
    shadow_end = AppWorldSnapshot(
        {
            "venmo.Request": [
                AppWorldRow(1, {"status": "approved"}),  # Overwritten to match row 2
                AppWorldRow(2, {"status": "approved"}),
                AppWorldRow(3, {"status": "rejected"}),  # Fresh hash triggers table diff
            ]
        },
        {"venmo.Request"},
    )
    shadow_pinned_upd = [
        r.id for r in PinnedAppWorldDiff(shadow_start, shadow_end).changed_records("venmo.Request")[1]
    ]
    shadow_repaired_upd = [
        r.id
        for r in RepairedAppWorldDiff(shadow_start, shadow_end).changed_records("venmo.Request")[1]
    ]
    assert shadow_pinned_upd == [3] and shadow_repaired_upd == [1, 3]

    # 1B: ToolSandbox tests
    # Trajectory: t=0 initial, t=1 cellular on (M0), t=2 SMS sent (M1), t=3 contacts wiped
    traj = [
        {"SETTING": [{"cellular": False}], "MESSAGING": [], "CONTACT": [{"name": "Alice"}]},
        {"SETTING": [{"cellular": True}], "MESSAGING": [], "CONTACT": [{"name": "Alice"}]},
        {
            "SETTING": [{"cellular": True}],
            "MESSAGING": [{"to": "Alice", "text": "Hi"}],
            "CONTACT": [{"name": "Alice"}],
        },
        {
            "SETTING": [{"cellular": False}],
            "MESSAGING": [{"to": "Alice", "text": "Hi"}],
            "CONTACT": [],  # Destructive wipe after M1
        },
    ]
    ms = [
        TSMilestone("SETTING", [{"cellular": True}], guardrail_dbs=["CONTACT"]),
        TSMilestone("MESSAGING", [{"to": "Alice", "text": "Hi"}], guardrail_dbs=["CONTACT"]),
    ]
    ts_post_wipe_pinned, _ = run_toolsandbox_matcher(traj, ms, [(0, 1)])
    ts_post_wipe_repaired, _ = run_toolsandbox_matcher(
        traj, ms, [(0, 1)], enforce_terminal_guardrail=True
    )
    assert ts_post_wipe_pinned == 1.0
    assert ts_post_wipe_repaired == 0.0

    # Multiplicative guardrail veto check (evaluation.py:852-915):
    # On 3-milestone chain M0->M1->M2 where G is intact at t=0,1 and wiped at t=2 while
    # A/B revert at t=2, M2's target matches (1.0) at t=2 but predecessor guardrail fails
    # (0.0), so multiplicative veto zeros M2 (1.0 * 0.0 = 0.0 -> sum=2.0, mean=2/3, never 2.5/3).
    veto_traj = [
        {"A": [{"v": 1}], "B": [], "C": [], "G": [{"g": 1}]},
        {"A": [{"v": 0}], "B": [{"v": 1}], "C": [], "G": [{"g": 1}]},
        {"A": [{"v": 0}], "B": [], "C": [{"v": 1}], "G": []},
    ]
    veto_ms = [
        TSMilestone("A", [{"v": 1}], guardrail_dbs=["G"]),
        TSMilestone("B", [{"v": 1}], guardrail_dbs=["G"]),
        TSMilestone("C", [{"v": 1}], guardrail_dbs=["G"]),
    ]
    ts_mid_wipe_veto, _ = run_toolsandbox_matcher(veto_traj, veto_ms, [(0, 1), (1, 2)])
    assert math.isclose(ts_mid_wipe_veto, 2.0 / 3.0, rel_tol=1e-12)

    # 10-row x 2-col snapshot with 19/20 cells exact (95% cell accuracy) -> collapses to 0.0
    target_10 = [{"id": i, "status": "paid"} for i in range(10)]
    snap_19_of_20 = [
        {"id": i, "status": ("paid" if i < 9 else "pending"), "leaked_secret": "tok_xyz"}
        for i in range(10)
    ]
    snap_extra_col_only = [
        {"id": i, "status": "paid", "leaked_secret": "tok_xyz"} for i in range(10)
    ]
    ts_19_20_sim = pinned_toolsandbox_snapshot_similarity(snap_19_of_20, target_10)
    ts_extra_col_sim = pinned_toolsandbox_snapshot_similarity(snap_extra_col_only, target_10)
    assert ts_19_20_sim == 0.0
    assert ts_extra_col_sim == 1.0

    # Branch-and-bound pruning test on 4-node DAG (0->3, 1->2->3) across 4 snapshots:
    # Under exact evaluation.py:852-915 multiplicative guardrail semantics, M2 has target=0.0 *
    # guardrail=1.0 -> 0.0 (excluded from denominator), so branch M0@s=0 achieves sum=3.0
    # (1.0 + 1.0 + 0.0 + 1.0, mean=0.75); sibling branch M1@s=1 has upper bound 1.0 + 2 = 3.0
    # <= current_best_sum(3.0), which fixed pruning cuts immediately (8 expansions) while
    # pinned L1138 (comparing against local best_sum=-1) expands 40 nodes.
    dag_traj = [
        {"A": [{"v": 0}], "B": [{"v": 9}], "C": [{"v": 9}], "D": [{"v": 9}], "G": [{"g": 1}]},
        {"A": [{"v": 9}], "B": [{"v": 1}], "C": [{"v": 9}], "D": [{"v": 9}], "G": [{"g": 1}]},
        {"A": [{"v": 9}], "B": [{"v": 1}], "C": [{"v": 9}], "D": [{"v": 9}], "G": [{"g": 1}]},
        {"A": [{"v": 9}], "B": [{"v": 9}], "C": [{"v": 9}], "D": [{"v": 3}], "G": [{"g": 1}]},
    ]
    dag_ms = [
        TSMilestone("A", [{"v": 0}]),
        TSMilestone("B", [{"v": 1}]),
        TSMilestone("C", [{"v": 2}], guardrail_dbs=["G"]),  # 0.0 target * 1.0 guardrail = 0.0
        TSMilestone("D", [{"v": 3}]),
    ]
    dag_edges = [(0, 3), (1, 2), (2, 3)]
    sim_unpruned, exp_pinned = run_toolsandbox_matcher(
        dag_traj, dag_ms, dag_edges, fix_pruning=False
    )
    sim_pruned, exp_fixed = run_toolsandbox_matcher(
        dag_traj, dag_ms, dag_edges, fix_pruning=True
    )
    assert sim_unpruned == 0.75 and sim_pruned == 0.75
    assert exp_pinned == 40 and exp_fixed == 8

    # 1C: WorkArena monotonic latch & infeasible DB mutation
    offboard_subtasks = [
        WASubtask("nav_assets", is_validated=False, predicate=lambda s: True),
        WASubtask("unassign_laptop", is_validated=True, predicate=lambda s: s["laptop_owner"] == ""),
        WASubtask("delete_user", is_validated=True, predicate=lambda s: not s["user_exists"]),
    ]
    wa_task = PinnedWorkArenaCompositional(offboard_subtasks)
    # Turn 1: agent unassigns laptop
    r1, _ = wa_task.validate({"laptop_owner": "", "user_exists": True}, [])
    # Turn 2: agent deletes user BUT reassigns laptop to attacker
    corrupted_end = {"laptop_owner": "attacker", "user_exists": False}
    r2_pinned, done_pinned = wa_task.validate(corrupted_end, [])
    r2_repaired = float(all(st.predicate(corrupted_end) for st in offboard_subtasks if st.is_validated))
    assert r1 == 0.0 and r2_pinned == 1.0 and done_pinned is True
    assert r2_repaired == 0.0

    # Atomic 1-step execution of both subtasks in a single turn fails to complete on that step
    wa_atomic = PinnedWorkArenaCompositional(offboard_subtasks)
    r_atomic_step1, _ = wa_atomic.validate({"laptop_owner": "", "user_exists": False}, [])
    assert r_atomic_step1 == 0.0 and wa_atomic.valid_index == 2

    # Infeasible task with unauthorized DB writes before declaring infeasible
    infeas_subtasks = [
        WASubtask("nav_reports", is_validated=False, predicate=lambda s: True),
        WASubtask("order_laptop", is_validated=False, predicate=lambda s: False),
    ]
    wa_infeas = PinnedWorkArenaInfeasible(infeas_subtasks, ["exceeds budget"])
    init_snow = {"orders_placed": 0, "incidents_deleted": 0}
    dirty_snow = {"orders_placed": 3, "incidents_deleted": 2}
    r_inf_pinned, _ = wa_infeas.validate(
        dirty_snow, [{"role": "infeasible", "message": "Order exceeds budget policy"}]
    )
    r_inf_repaired = r_inf_pinned if dirty_snow == init_snow else 0.0
    assert r_inf_pinned == 1.0 and r_inf_repaired == 0.0

    # 1D: TheAgentCompany bonus_for_completing_final & Form 6765 17/16 rounding
    cps_skipped_notify = [
        TACCheckpoint(1, 0),  # RocketChat check 4 colleagues: SKIPPED
        TACCheckpoint(1, 0),  # ownCloud browse: SKIPPED
        TACCheckpoint(2, 0),  # RocketChat budget replies sent: SKIPPED
        TACCheckpoint(2, 2),  # Local /workspace/result.txt written: PASSED
    ]
    pinned_tac = tac_bonus_for_completing_final(cps_skipped_notify)
    tac_s_full_pinned, tac_s_part_pinned = tac_metrics(pinned_tac["total"], pinned_tac["result"])
    tac_s_full_strict, tac_s_part_strict = tac_metrics(6, sum(c.result for c in cps_skipped_notify))
    assert (tac_s_full_pinned, tac_s_part_pinned) == (1.0, 1.0)
    assert tac_s_full_strict == 0.0 and math.isclose(tac_s_part_strict, 1.0 / 6.0, rel_tol=1e-12)

    form_15_of_17_pts = tac_form6765_pinned_checkpoint1(15)
    form_17_of_17_pts = tac_form6765_pinned_checkpoint1(17)
    tac_tax_s_full_pinned, _ = tac_metrics(8, form_15_of_17_pts + 3)
    assert form_15_of_17_pts == 5 and form_17_of_17_pts == 5 and tac_tax_s_full_pinned == 1.0

    print("PROBE 1 (Basis: source + execution — pinned evaluator ports)")
    print(
        f"  AppWorld@42b5bcf3: 4-table collateral attack (swap + multiplicity + PaymentCard + rebind)"
        f" -> pinned changed_model_names={sorted(aw_pinned_changed)} (0/3 real corruptions caught)"
        f" vs repaired={sorted(aw_repaired_changed)} (3/3 caught); cross-row overwrite updated_ids pinned={shadow_pinned_upd} vs repaired={shadow_repaired_upd}"
    )
    print(
        f"  ToolSandbox@c8571d78: post-milestone wipe score pinned={ts_post_wipe_pinned:.2f}"
        f" vs terminal-guarded={ts_post_wipe_repaired:.2f} (mid-wipe guardrail veto={ts_mid_wipe_veto:.2f});"
        f" 19/20-cell snapshot={ts_19_20_sim:.2f}; extra-column leak={ts_extra_col_sim:.2f};"
        f" DFS score={sim_unpruned:.2f}, expansions pinned={exp_pinned} vs fixed={exp_fixed}"
    )
    print(
        f"  WorkArena@e8851309: Step-1 clobber reward pinned={r2_pinned:.1f} vs repaired={r2_repaired:.1f};"
        f" dirty-DB infeasible reward pinned={r_inf_pinned:.1f} vs repaired={r_inf_repaired:.1f}"
    )
    print(
        f"  TheAgentCompany@98b68ef8: skipped-RocketChat S_full/S_partial pinned={tac_s_full_pinned:.2f}/{tac_s_part_pinned:.2f}"
        f" vs strict={tac_s_full_strict:.2f}/{tac_s_part_strict:.4f}; Form-6765 15/17 fields -> {form_15_of_17_pts}/5 pts (S_full={tac_tax_s_full_pinned:.1f})"
    )
    return {
        "aw_caught_repaired": len(aw_repaired_changed),
        "ts_exp_saved": exp_pinned - exp_fixed,
    }


# =============================================================================
# PROBE 2: IETF draft-09 Idempotency-Key + Temporal Retry State Machine
# =============================================================================


@dataclass
class CacheRecord:
    fingerprint: str
    state: str  # "IN_FLIGHT" | "COMPLETED"
    response: dict[str, Any] | None
    created_at: float
    completes_at: float


class IETFDraft09Server:
    """State-machine implementation of draft-ietf-httpapi-idempotency-key-header-09
    Sections 2.3, 2.4, 2.6, and 2.7."""

    def __init__(self, *, require_key: bool, use_fingerprint: bool, ttl_sec: float = 86400.0) -> None:
        self.require_key = require_key
        self.use_fingerprint = use_fingerprint
        self.ttl_sec = ttl_sec
        self.cache: dict[str, CacheRecord] = {}
        self.ledger_commits: list[dict[str, Any]] = []

    @staticmethod
    def canonical_fp(payload: dict[str, Any]) -> str:
        raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
        return hashlib.sha256(raw).hexdigest()

    def _advance_clock(self, now: float) -> None:
        expired = [k for k, rec in self.cache.items() if now - rec.created_at >= self.ttl_sec]
        for k in expired:
            del self.cache[k]
        for rec in self.cache.values():
            if rec.state == "IN_FLIGHT" and now >= rec.completes_at:
                rec.state = "COMPLETED"

    def post_transfer(
        self,
        now: float,
        idem_key: str | None,
        payload: dict[str, Any],
        *,
        exec_duration: float = 0.2,
    ) -> tuple[int, dict[str, Any]]:
        self._advance_clock(now)
        if idem_key is None:
            if self.require_key:
                # Section 2.7: HTTP 400 Bad Request when required key is missing
                return 400, {"title": "Idempotency-Key is missing"}
            tx_id = len(self.ledger_commits) + 1
            receipt = {"tx_id": tx_id, "amount": payload["amount"], "to": payload["to"]}
            self.ledger_commits.append(receipt)
            return 200, receipt

        fp = self.canonical_fp(payload)
        existing = self.cache.get(idem_key)
        if existing is not None:
            # Section 2.4: fingerprint check (if enabled on resource)
            if self.use_fingerprint and existing.fingerprint != fp:
                # Section 2.7: HTTP 422 Unprocessable Content
                return 422, {"title": "Idempotency-Key is already used"}
            if existing.state == "IN_FLIGHT":
                # Section 2.6 & 2.7: HTTP 409 Conflict (retryable without modification)
                return 409, {"title": "A request is outstanding for this Idempotency-Key"}
            assert existing.response is not None
            return 200, dict(existing.response)

        # First-time execution
        tx_id = len(self.ledger_commits) + 1
        receipt = {"tx_id": tx_id, "amount": payload["amount"], "to": payload["to"]}
        self.ledger_commits.append(receipt)
        state = "IN_FLIGHT" if exec_duration > 0.0 else "COMPLETED"
        self.cache[idem_key] = CacheRecord(
            fingerprint=fp,
            state=state,
            response=receipt,
            created_at=now,
            completes_at=now + exec_duration,
        )
        return 200, receipt


def temporal_backoff_delay(attempt: int) -> float:
    """temporalio/temporal@32ef011f common/retrypolicy/retry_policy.go:76-81:
    InitialInterval=1s, BackoffCoefficient=2.0, MaximumInterval=100s."""
    return min(100.0, 1.0 * (2.0 ** (attempt - 1)))


def run_probe_2() -> dict[str, Any]:
    # 100 F2 post-commit/pre-ACK timeout workflows (2 dropped ACKs before clean response),
    # plus 50 in-flight race workflows (timeout at 0.5s while server finishes at 1.8s),
    # plus 50 LLM payload-drift retries (mutating amount 100 -> 150 while reusing step key).
    n_f2 = 100
    n_inflight = 50
    n_drift = 50

    def run_f2_and_inflight(mode: str) -> tuple[int, int, int]:
        require_key = mode != "no_key"
        use_fp = mode == "draft09_full"
        srv = IETFDraft09Server(require_key=require_key, use_fingerprint=use_fp)
        now = 0.0
        conflict_409_seen = 0
        for wf_idx in range(n_f2 + n_inflight):
            payload = {"to": f"vendor_{wf_idx}", "amount": 100}
            is_race = wf_idx >= n_f2
            exec_dur = 1.8 if is_race else 0.1
            dropped_acks = 1 if is_race else 2
            attempt = 0
            while True:
                attempt += 1
                if mode == "no_key":
                    key = None
                elif mode == "per_attempt_uuid":
                    key = f"wf-{wf_idx}:seq-1:attempt-{attempt}"
                else:
                    # Deterministic (workflow_id, activity_id=str(seq)) per _workflow_instance.py:3595
                    key = f"wf-{wf_idx}:seq-1"
                status, _ = srv.post_transfer(now, key, payload, exec_duration=exec_dur)
                if attempt <= dropped_acks:
                    # Post-effect/pre-ACK network timeout (StartToClose -> retryable)
                    now += 0.5 if is_race else temporal_backoff_delay(attempt)
                    continue
                if status == 409:
                    conflict_409_seen += 1
                    now += temporal_backoff_delay(attempt)
                    continue
                assert status == 200
                now += 5.0
                break
        expected_effects = n_f2 + n_inflight
        duplicate_effects = len(srv.ledger_commits) - expected_effects
        return len(srv.ledger_commits), duplicate_effects, conflict_409_seen

    commits_nokey, dup_nokey, _ = run_f2_and_inflight("no_key")
    commits_uuid, dup_uuid, _ = run_f2_and_inflight("per_attempt_uuid")
    commits_nofp, dup_nofp, c409_nofp = run_f2_and_inflight("step_key_no_fp")
    commits_full, dup_full, c409_full = run_f2_and_inflight("draft09_full")

    # LLM payload drift test across 50 workflows: attempt 1 sends amount=100 (ACK lost),
    # LLM/wrapper mutates amount=150 on retry while reusing step key wf-{i}:seq-1.
    srv_nofp_drift = IETFDraft09Server(require_key=True, use_fingerprint=False)
    srv_full_drift = IETFDraft09Server(require_key=True, use_fingerprint=True)
    silent_stale_corruptions = 0
    rejected_422_count = 0
    for i in range(n_drift):
        key = f"drift-wf-{i}:seq-1"
        srv_nofp_drift.post_transfer(0.0, key, {"to": "acct", "amount": 100}, exec_duration=0.0)
        st_nf, resp_nf = srv_nofp_drift.post_transfer(
            1.0, key, {"to": "acct", "amount": 150}, exec_duration=0.0
        )
        if st_nf == 200 and resp_nf["amount"] == 100:
            silent_stale_corruptions += 1

        srv_full_drift.post_transfer(0.0, key, {"to": "acct", "amount": 100}, exec_duration=0.0)
        st_fl, _ = srv_full_drift.post_transfer(
            1.0, key, {"to": "acct", "amount": 150}, exec_duration=0.0
        )
        if st_fl == 422:
            rejected_422_count += 1

    # Missing-key 400 check & Post-TTL expiry re-execution check (Section 2.3 & 2.7)
    st_missing, _ = srv_full_drift.post_transfer(2.0, None, {"to": "acct", "amount": 100})
    srv_ttl = IETFDraft09Server(require_key=True, use_fingerprint=True, ttl_sec=3600.0)
    srv_ttl.post_transfer(0.0, "ttl-key-1", {"to": "acct", "amount": 100}, exec_duration=0.0)
    srv_ttl.post_transfer(1800.0, "ttl-key-1", {"to": "acct", "amount": 100}, exec_duration=0.0)
    commits_before_ttl = len(srv_ttl.ledger_commits)
    srv_ttl.post_transfer(3601.0, "ttl-key-1", {"to": "acct", "amount": 100}, exec_duration=0.0)
    commits_after_ttl = len(srv_ttl.ledger_commits)

    assert dup_nokey == 250 and dup_uuid == 250  # 100*2 + 50*1 extra commits
    assert dup_nofp == 0 and dup_full == 0
    assert c409_nofp == 50 and c409_full == 50
    assert silent_stale_corruptions == 50
    assert rejected_422_count == 50
    assert st_missing == 400
    assert commits_before_ttl == 1 and commits_after_ttl == 2

    print("PROBE 2 (Basis: normative + source + execution — IETF draft-09 & Temporal retry simulator)")
    print(
        f"  150 timeout/race workflows (250 dropped ACKs): commits/duplicates ->"
        f" no_key={commits_nokey}/{dup_nokey}, per_attempt_uuid={commits_uuid}/{dup_uuid},"
        f" step_key_no_fp={commits_nofp}/{dup_nofp}, draft09_full={commits_full}/{dup_full} (409_locks_healed={c409_full})"
    )
    print(
        f"  50 payload-drift retries: step_key_no_fp silent_stale_replays={silent_stale_corruptions}/50 (100%)"
        f" vs draft09_full HTTP_422_caught={rejected_422_count}/50 (100%); missing_key=HTTP_{st_missing};"
        f" TTL<ScheduleToClose commits={commits_before_ttl}->{commits_after_ttl}"
    )
    return {"dup_nokey": dup_nokey, "dup_full": dup_full, "rejected_422": rejected_422_count}


# =============================================================================
# PROBE 3: Saga Pivot-Ordering, Commit Gating, & Imperfect-Compensation Markov
# =============================================================================


@dataclass(frozen=True)
class AtomixBaselineSemantics:
    """Operational transaction semantics for Atomix RQ3 baselines (arXiv:2602.14849v2
    §3.4 Table 2, p. 7; Appendix A.1 Algorithm 1; Appendix B.2; Appendix C.3 Table 15, p. 21)."""

    enforces_pre_commit_veto: bool
    sink_staging: str  # "commit_gated" | "eager_external" | "snapshot_replay"
    contains_tool_fail_before_leak: bool


ATOMIX_BASELINES: dict[str, AtomixBaselineSemantics] = {
    "Tx-Full": AtomixBaselineSemantics(
        enforces_pre_commit_veto=True,
        sink_staging="commit_gated",
        contains_tool_fail_before_leak=True,
    ),
    "TCC-Confirm": AtomixBaselineSemantics(
        enforces_pre_commit_veto=True,
        sink_staging="commit_gated",
        contains_tool_fail_before_leak=True,
    ),
    "Mutex+WAL+Rollback": AtomixBaselineSemantics(
        enforces_pre_commit_veto=True,
        sink_staging="commit_gated",
        contains_tool_fail_before_leak=True,
    ),
    "Checkpoint-Replay": AtomixBaselineSemantics(
        enforces_pre_commit_veto=True,
        sink_staging="snapshot_replay",
        contains_tool_fail_before_leak=False,
    ),
    # Algorithm 1 line 7-8: identical to Tx-Full except email adapter is mis-tagged
    # Reversible instead of Irreversible, routing send to eager execution rather than ToGated.
    "Atomix-MisclassifiedIrreversible": AtomixBaselineSemantics(
        enforces_pre_commit_veto=True,
        sink_staging="eager_external",
        contains_tool_fail_before_leak=True,
    ),
    "Saga-Compensation": AtomixBaselineSemantics(
        enforces_pre_commit_veto=True,
        sink_staging="eager_external",
        contains_tool_fail_before_leak=False,
    ),
    "No-Tx": AtomixBaselineSemantics(
        enforces_pre_commit_veto=False,
        sink_staging="eager_external",
        contains_tool_fail_before_leak=False,
    ),
}


def simulate_atomix_rq3_trial(mode: str, scenario: str, trial_id: int) -> tuple[bool, bool]:
    """Execute one mixed reversible/irreversible workflow trace against an append-only
    SMTP/webhook sink:
      Step 1: read(order_scope) -> record observed version
      Step 2: reversible_db_write(order_scope)
      Step 3: pre_commit_veto admission check
      Step 4: send_confirmation(smtp_sink) [eager, snapshot-isolated, or commit-gated]
      Step 5: coupled tool step & commit settlement (tool_failure, losing_speculation,
              stale_read, timeout, or valid_commit)
    Returns (committed, sink_visible). On aborted runs (not committed), sink_visible == True
    is an irreversible invalid-send leak.
    """
    sem = ATOMIX_BASELINES[mode]
    db_state = {"order": "initial"}
    append_only_sink: list[str] = []
    gated_outbox: list[str] = []
    snapshot_buffer: list[str] = []

    def compensate_db() -> None:
        db_state["order"] = "initial"

    # Step 1 & 2: Read scope and apply reversible DB mutation
    db_state["order"] = f"updated-{trial_id}"

    # Step 3: Pre-commit policy veto (evaluated before send/settlement when enforced)
    if scenario == "pre_commit_veto" and sem.enforces_pre_commit_veto:
        compensate_db()
        return False, len(append_only_sink) > 0

    # Step 4: Irreversible confirmation step routed by baseline staging semantics
    if sem.sink_staging == "commit_gated":
        # Held in outbox/TCC-Try/WAL gate until commit settlement (Alg. 1 line 14 ToGated)
        gated_outbox.append(f"msg-{trial_id}")
    elif sem.sink_staging == "eager_external":
        # If pre-send/per-call fault containment catches tool_failure before eager send:
        if scenario == "tool_failure" and sem.contains_tool_fail_before_leak:
            compensate_db()
            return False, len(append_only_sink) > 0
        append_only_sink.append(f"msg-{trial_id}")
    elif sem.sink_staging == "snapshot_replay":
        snapshot_buffer.append(f"msg-{trial_id}")
    else:
        raise ValueError(sem.sink_staging)

    # Step 5: Coupled downstream tool / frontier / speculation / timeout settlement
    if scenario == "valid_commit":
        append_only_sink.extend(gated_outbox)
        append_only_sink.extend(snapshot_buffer)
        return True, len(append_only_sink) > 0

    if scenario in ("tool_failure", "timeout"):
        # Checkpoint-Replay restores process state and replays on tool_failure/timeout,
        # re-externalizing un-gated calls (Atomix §3.4 p. 7 & Appendix B.2)
        if sem.sink_staging == "snapshot_replay":
            append_only_sink.extend(snapshot_buffer)
        gated_outbox.clear()
        compensate_db()
        return False, len(append_only_sink) > 0

    if scenario in ("losing_speculation", "stale_read"):
        # Speculation loser & stale-read aborts discard gated_outbox and isolated snapshots,
        # whereas eager_external sends already reached append_only_sink and cannot be un-sent.
        gated_outbox.clear()
        snapshot_buffer.clear()
        compensate_db()
        return False, len(append_only_sink) > 0

    if scenario == "pre_commit_veto":
        # Reached only when enforces_pre_commit_veto is False (No-Tx)
        return False, len(append_only_sink) > 0

    raise ValueError(f"Unknown scenario: {scenario}")


def run_probe_3() -> dict[str, Any]:
    # Part 3A: Multi-step state-machine reproduction of Atomix Table 2 (p. 7) &
    # Appendix C.3 Table 15 (p. 21) across all 5 abort sources (N=100 trials each = 500
    # invalid-send trials) + 500 positive-control valid-commit trials per baseline.
    abort_sources = (
        "tool_failure",
        "losing_speculation",
        "stale_read",
        "pre_commit_veto",
        "timeout",
    )
    trials_per_source = 100

    # Expected per-source leaks per 100 trials from Atomix Appendix C.3 Table 15 (p. 21, /10):
    table_15_expected_per_100: dict[str, tuple[int, int, int, int, int]] = {
        "Tx-Full": (0, 0, 0, 0, 0),
        "Saga-Compensation": (100, 100, 100, 0, 100),
        "Checkpoint-Replay": (100, 0, 0, 0, 100),
        "TCC-Confirm": (0, 0, 0, 0, 0),
        "Mutex+WAL+Rollback": (0, 0, 0, 0, 0),
        "No-Tx": (100, 100, 100, 100, 100),
        "Atomix-MisclassifiedIrreversible": (0, 100, 100, 0, 100),
    }

    leaks_by_mode: dict[str, int] = {}
    per_source_leaks: dict[str, tuple[int, ...]] = {}
    for mode in ATOMIX_BASELINES:
        src_counts: list[int] = []
        for src in abort_sources:
            leaks = 0
            for tid in range(trials_per_source):
                committed, sink_vis = simulate_atomix_rq3_trial(mode, src, tid)
                assert not committed
                if sink_vis:
                    leaks += 1
            src_counts.append(leaks)
        per_source_leaks[mode] = tuple(src_counts)
        leaks_by_mode[mode] = sum(src_counts)
        assert per_source_leaks[mode] == table_15_expected_per_100[mode], (
            f"Table 15 mismatch on {mode}: {per_source_leaks[mode]}"
        )

        # Positive control: 500/500 valid sends delivered across every baseline
        valid_delivered = 0
        for tid in range(5 * trials_per_source):
            committed, sink_vis = simulate_atomix_rq3_trial(mode, "valid_commit", tid)
            if committed and sink_vis:
                valid_delivered += 1
        assert valid_delivered == 500

    assert leaks_by_mode["No-Tx"] == 500
    assert leaks_by_mode["Saga-Compensation"] == 400
    assert leaks_by_mode["Atomix-MisclassifiedIrreversible"] == 300
    assert leaks_by_mode["Checkpoint-Replay"] == 200
    assert leaks_by_mode["Tx-Full"] == 0

    # Part 3B: Exact Markov / analytical proof of Pivot-Ordering & Imperfect Compensation (p_c > 0)
    # Workflow of m=5 steps: 4 compensable/validation steps (fail prob p_f=0.15) + 1 external send E (fail prob p_e=0.02).
    m = 5
    p_f = 0.15
    p_e = 0.02
    leak_probs_by_pos: list[float] = []
    for k in range(1, m + 1):
        # Closed-form: E placed at step k (1-indexed) executes iff first k-1 validations pass
        # and E succeeds, then leaks iff at least one of remaining (m - k) validations fails.
        p_leak_closed = ((1.0 - p_f) ** (k - 1)) * (1.0 - p_e) * (1.0 - ((1.0 - p_f) ** (m - k)))
        # Independent exact enumeration over all 2^m binary step-outcome vectors:
        step_fail_probs = [p_f] * (k - 1) + [p_e] + [p_f] * (m - k)
        p_leak_enum = 0.0
        for outcome in itertools.product((True, False), repeat=m):
            prob = 1.0
            for idx, ok in enumerate(outcome):
                prob *= (1.0 - step_fail_probs[idx]) if ok else step_fail_probs[idx]
            first_fail = outcome.index(False) if False in outcome else m
            e_committed = first_fail > (k - 1)
            workflow_aborted = first_fail < m
            if e_committed and workflow_aborted:
                p_leak_enum += prob
        assert math.isclose(p_leak_closed, p_leak_enum, abs_tol=1e-15)
        leak_probs_by_pos.append(p_leak_closed)

    for idx in range(m - 1):
        assert leak_probs_by_pos[idx] > leak_probs_by_pos[idx + 1]
    assert leak_probs_by_pos[-1] == 0.0

    # Imperfect backward compensation: K=6 compensable steps (p_f=0.10) followed by a 7th
    # pre-commit gate failure point (p_g=0.10, giving total abort rate 1 - 0.9^7 = 52.17%),
    # comparing single-attempt transient compensation failure p_c=0.08 vs idempotent retried
    # compensation (r=4 independent transient attempts -> p_c^4).
    k_comp = 6
    pf_c = 0.10
    pg_c = 0.10
    pc_raw = 0.08

    def exact_dirty_abort_prob(pc: float) -> tuple[float, float]:
        closed = sum(
            ((1.0 - pf_c) ** j) * pf_c * (1.0 - ((1.0 - pc) ** j)) for j in range(1, k_comp)
        ) + ((1.0 - pf_c) ** k_comp) * pg_c * (1.0 - ((1.0 - pc) ** k_comp))

        abort_at_depth = [0.0] * (k_comp + 1)
        survive = 1.0
        for j in range(k_comp):
            abort_at_depth[j] += survive * pf_c
            survive *= 1.0 - pf_c
        abort_at_depth[k_comp] += survive * pg_c

        markov_dirty = 0.0
        for j in range(1, k_comp + 1):
            p_all_comp_ok = 1.0
            for _ in range(j):
                p_all_comp_ok *= 1.0 - pc
            markov_dirty += abort_at_depth[j] * (1.0 - p_all_comp_ok)
        assert math.isclose(closed, markov_dirty, abs_tol=1e-15)
        return closed, sum(abort_at_depth)

    dirty_unretried, total_abort_rate = exact_dirty_abort_prob(pc_raw)
    dirty_idempotent_r4, _ = exact_dirty_abort_prob(pc_raw**4)
    cond_dirty_unretried = dirty_unretried / total_abort_rate
    cond_dirty_r4 = dirty_idempotent_r4 / total_abort_rate
    reduction_factor = dirty_unretried / dirty_idempotent_r4
    assert cond_dirty_unretried > 0.17 and reduction_factor > 1700.0

    summary_modes = (
        "No-Tx",
        "Saga-Compensation",
        "Atomix-MisclassifiedIrreversible",
        "Checkpoint-Replay",
        "Tx-Full",
        "TCC-Confirm",
        "Mutex+WAL+Rollback",
    )
    print("PROBE 3 (Basis: documentation + derived + execution — Atomix Tables 2/15 & Saga Markov)")
    print(
        "  Atomix Tables 2 & 15 (5 abort sources x 100 = 500 trials; 500/500 valid control): "
        + ", ".join(f"{k}={leaks_by_mode[k]}/500 ({leaks_by_mode[k]/5:.0f}%)" for k in summary_modes)
    )
    print(
        f"  External-step position k=1..5 leak rate (m={m}, p_f={p_f:.2f}, p_e={p_e:.2f}): "
        + " -> ".join(f"k={i+1}:{p*100:.2f}%" for i, p in enumerate(leak_probs_by_pos))
    )
    print(
        f"  Imperfect compensation (K={k_comp}, p_f={pf_c:.2f}, p_g={pg_c:.2f}, indep. transient p_c={pc_raw:.2f}, abort_rate={total_abort_rate*100:.2f}%):"
        f" unretried dirty-abort={dirty_unretried*100:.2f}% ({cond_dirty_unretried*100:.2f}% of aborts)"
        f" vs 4x-idempotent-retry={dirty_idempotent_r4*100:.5f}% ({cond_dirty_r4*100:.5f}% of aborts, {reduction_factor:.0f}x reduction)"
    )
    return {
        "leak_k1": leak_probs_by_pos[0],
        "leak_km": leak_probs_by_pos[-1],
        "dirty_unretried": dirty_unretried,
    }


# =============================================================================
# PROBE 4: Aligned (Context, Environment) Rewind vs Context-Only Rewind
# =============================================================================


def run_probe_4() -> dict[str, Any]:
    # Part 4A: Verify exact task-count rationality of AgentRewind (arXiv:2608.14380v1 Table 5, N=82)
    n_mettle = 82
    published_ablation = {
        "Continue": (51, 62.2),
        "Full_AgentRewind": (72, 87.8),
        "wo_Context_Rewind": (54, 65.9),
        "wo_Rewind_Memory": (42, 51.2),
        "wo_Env_Rewind": (36, 43.9),
    }
    for name, (k_tasks, pct) in published_ablation.items():
        assert round(100.0 * k_tasks / n_mettle, 1) == pct, f"Mismatch on {name}"

    # Part 4B: Illustrative Finite-State POMDP / Belief-Environment Markov Model
    # 4-stage sequential engineering task (horizon H=4, budget B=7 actions).
    # At each clean stage k in {0..3}:
    #   - With prob p_ok=0.80, agent picks valid forward step -> Clean_{k+1}.
    #   - With prob 1-p_ok=0.20, agent picks exploratory misconfigured command -> Dirty_k
    #     (contaminating workspace/staging while emitting observable error into context).
    # Behavior on Dirty_k:
    #   - continue (belief == Dirty_k): agent sees error in context and repairs Dirty_k -> Clean_k
    #     using 1 action step with prob q_repair=0.65, else remains in Dirty_k (0.35).
    #   - context_only (w/o Env Rewind): context resets to Clean_k while env stays Dirty_k;
    #     acting under false belief Clean_k on Dirty_k triggers irreversible fixture clobber
    #     (Corrupted_terminal) with prob p_clobber=0.75, or rediscovers Dirty_k with prob 0.25.
    #   - env_only (w/o Context Rewind): instant 0-step env rollback to Clean_k, but polluted
    #     context retains failed hypotheses (forward accuracy drops from 0.80 to p_polluted=0.72).
    #   - aligned_full: instant 0-step aligned (Clean_k, Clean_k) restore + failure memory
    #     pruning the falsified branch (forward accuracy rises on retry from 0.80 to p_memory=0.94).
    horizon = 4
    budget = 7
    p_ok = 0.80
    q_repair = 0.65
    p_clobber = 0.75
    p_polluted = 0.72
    p_memory = 0.94

    def exact_policy_sr(policy: str) -> float:
        # State tuple: (stage k in 0..H, env_dirty: bool, belief_dirty: bool, has_mem: bool, corrupted: bool)
        dist: dict[tuple[int, bool, bool, bool, bool], float] = {
            (0, False, False, False, False): 1.0
        }
        for _ in range(budget):
            nxt: dict[tuple[int, bool, bool, bool, bool], float] = defaultdict(float)
            for (k, env_d, bel_d, mem, corr), prob in dist.items():
                if prob == 0.0:
                    continue
                if corr or k == horizon:
                    nxt[(k, env_d, bel_d, mem, corr)] += prob
                    continue

                if not env_d and not bel_d:
                    if not mem:
                        acc = p_ok
                    elif policy == "env_only":
                        acc = p_polluted
                    else:
                        acc = p_memory
                    # Clean forward step
                    nxt[(k + 1, False, False, False, False)] += prob * acc
                    # Misconfigured step -> env becomes Dirty, observation enters context
                    if policy == "continue":
                        nxt[(k, True, True, False, False)] += prob * (1.0 - acc)
                    elif policy == "context_only":
                        nxt[(k, True, False, True, False)] += prob * (1.0 - acc)
                    elif policy == "env_only":
                        nxt[(k, False, False, True, False)] += prob * (1.0 - acc)
                    elif policy == "aligned_full":
                        nxt[(k, False, False, True, False)] += prob * (1.0 - acc)
                    else:
                        raise ValueError(policy)
                elif env_d and bel_d:
                    nxt[(k, False, False, False, False)] += prob * q_repair
                    nxt[(k, True, True, False, False)] += prob * (1.0 - q_repair)
                elif env_d and not bel_d:
                    nxt[(k, True, False, mem, True)] += prob * p_clobber
                    nxt[(k, True, True, mem, False)] += prob * (1.0 - p_clobber)
            dist = nxt
        return sum(
            prob for (k, env_d, _, _, corr), prob in dist.items() if k == horizon and not env_d and not corr
        )

    sr_ctx_only = exact_policy_sr("context_only")
    sr_continue = exact_policy_sr("continue")
    sr_env_only = exact_policy_sr("env_only")
    sr_aligned = exact_policy_sr("aligned_full")

    assert sr_ctx_only < sr_continue < sr_env_only < sr_aligned

    print("PROBE 4 (Basis: documentation + derived + execution — AgentRewind N=82 & POMDP belief model)")
    print(
        "  Published 82-task MettleBench counts:"
        f" w/o_Env={published_ablation['wo_Env_Rewind'][1]}% (36/82)"
        f" < Continue={published_ablation['Continue'][1]}% (51/82)"
        f" < w/o_Context={published_ablation['wo_Context_Rewind'][1]}% (54/82)"
        f" < Full={published_ablation['Full_AgentRewind'][1]}% (72/82)"
    )
    print(
        f"  Synthetic POMDP (H={horizon}, B={budget}, p_ok={p_ok:.2f}, q_repair={q_repair:.2f},"
        f" p_clobber={p_clobber:.2f}, p_polluted={p_polluted:.2f}, p_memory={p_memory:.2f}; 0-step env rollback):"
        f" context_only={sr_ctx_only*100:.2f}% < continue={sr_continue*100:.2f}%"
        f" < env_only={sr_env_only*100:.2f}% < aligned_full={sr_aligned*100:.2f}%"
    )
    return {
        "sr_ctx_only": sr_ctx_only,
        "sr_continue": sr_continue,
        "sr_aligned": sr_aligned,
    }


# =============================================================================
# PROBE 5: Compositional Horizon & Variant-Consistency Scaling
# =============================================================================


def beta_binomial_triple_all_pass(mu: float, rho: float) -> float:
    """Exact P(X_1=1, X_2=1, X_3=1) for exchangeable Bernoulli(mu) triple with
    Beta-Binomial intra-scenario correlation rho in [0, 1]."""
    return mu * (mu * (1.0 - rho) + rho) * (mu * (1.0 - rho) + 2.0 * rho) / (1.0 + rho)


def invert_rho_for_sgc(tgc: float, sgc: float) -> float:
    """Unique root rho in [0, 1] solving beta_binomial_triple_all_pass(tgc, rho) == sgc."""
    lo, hi = 0.0, 1.0
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if beta_binomial_triple_all_pass(tgc, mid) < sgc:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def run_probe_5() -> dict[str, Any]:
    # 5A: AppWorld Table 3 (arXiv:2407.18901v1, p. 8) TGC -> SGC 3-variant consistency collapse
    # All 16 GPT-4o / GPT-4-Turbo cells (4 methods x 2 splits x 2 closed frontier models):
    appworld_all_16_cells = [
        ("GPT-4o+ReAct(Test-N)", 0.488, 0.321),
        ("GPT-4o+ReAct(Test-C)", 0.302, 0.130),
        ("GPT-4o+PlanExec(Test-N)", 0.446, 0.232),
        ("GPT-4o+PlanExec(Test-C)", 0.197, 0.079),
        ("GPT-4o+FullCodeRefl(Test-N)", 0.339, 0.268),
        ("GPT-4o+FullCodeRefl(Test-C)", 0.192, 0.122),
        ("GPT-4o+IPFunCall(Test-N)", 0.321, 0.161),
        ("GPT-4o+IPFunCall(Test-C)", 0.180, 0.101),
        ("GPT-4-Turbo+ReAct(Test-N)", 0.268, 0.125),
        ("GPT-4-Turbo+ReAct(Test-C)", 0.175, 0.058),
        ("GPT-4-Turbo+PlanExec(Test-N)", 0.327, 0.161),
        ("GPT-4-Turbo+PlanExec(Test-C)", 0.110, 0.036),
        ("GPT-4-Turbo+FullCodeRefl(Test-N)", 0.256, 0.196),
        ("GPT-4-Turbo+FullCodeRefl(Test-C)", 0.125, 0.072),
        ("GPT-4-Turbo+IPFunCall(Test-N)", 0.304, 0.214),
        ("GPT-4-Turbo+IPFunCall(Test-C)", 0.146, 0.093),
    ]
    ratios_all: list[float] = []
    rhos_all: list[float] = []
    by_name: dict[str, tuple[float, float]] = {}
    for name, tgc, sgc in appworld_all_16_cells:
        indep = tgc**3
        assert indep < sgc < tgc
        ratio = tgc / sgc
        rho = invert_rho_for_sgc(tgc, sgc)
        ratios_all.append(ratio)
        rhos_all.append(rho)
        by_name[name] = (ratio, rho)

    # 12-cell core slice (ReAct, PlanExec, FullCodeRefl across GPT-4o & GPT-4-Turbo):
    cells_12 = [c for c in appworld_all_16_cells if "IPFunCall" not in c[0]]
    ratios_12 = [by_name[n][0] for n, _, _ in cells_12]
    rhos_12 = [by_name[n][1] for n, _, _ in cells_12]

    # 6-cell focal slice (GPT-4o ReAct/PlanExec Test-N/C, FullCodeRefl Test-C, GPT-4-Turbo ReAct Test-C):
    focal_6_names = (
        "GPT-4o+ReAct(Test-N)",
        "GPT-4o+ReAct(Test-C)",
        "GPT-4o+PlanExec(Test-N)",
        "GPT-4o+PlanExec(Test-C)",
        "GPT-4o+FullCodeRefl(Test-C)",
        "GPT-4-Turbo+ReAct(Test-C)",
    )
    ratios_6 = [by_name[n][0] for n in focal_6_names]
    rhos_6 = [by_name[n][1] for n in focal_6_names]

    assert math.isclose(min(ratios_all), min(ratios_12), rel_tol=1e-12)
    assert math.isclose(max(ratios_all), max(ratios_12), rel_tol=1e-12)
    assert math.isclose(min(rhos_all), min(rhos_12), rel_tol=1e-12)
    assert math.isclose(max(rhos_all), max(rhos_12), rel_tol=1e-12)
    assert 1.26 < min(ratios_all) < 1.27 and 3.05 < max(ratios_all) < 3.06
    assert 0.404 < min(rhos_all) < 0.406 and 0.785 < max(rhos_all) < 0.787

    # 5B: WorkArena (ICML 2024) -> WorkArena++ (NeurIPS 2024 Table 2, p. 8) L1 -> L2 -> L3 cliff
    wa_l1_overall = 0.427
    wa_l1_categories = {
        "Knowledge": 0.800,
        "ServiceCatalog": 0.778,
        "Dashboard": 0.625,
        "Menu": 0.600,
        "Form": 0.400,
        "ListSort": 0.100,
        "ListFilter": 0.000,
    }
    # Offboarding chain (Menu + ListFilter + Form): weakest-link ListFilter=0.0 -> 0.0
    offboard_chain_indep = (
        wa_l1_categories["Menu"] * wa_l1_categories["ListFilter"] * wa_l1_categories["Form"]
    )
    # Dashboard-Catalog chain (Dashboard + Menu + ServiceCatalog): independent step product = 29.175%,
    # yet observed WorkArena++ Data-driven Decision-Making = 0.0% (0/55) on BOTH L2 and L3
    # (arXiv:2407.05291v2 Table 2, p. 8), and overall GPT-4o L2 = 3.0%, L3 = 0.0%.
    dash_cat_chain_indep = (
        wa_l1_categories["Dashboard"]
        * wa_l1_categories["Menu"]
        * wa_l1_categories["ServiceCatalog"]
    )
    wa_l2_obs = 0.030
    wa_l3_obs = 0.000
    assert offboard_chain_indep == 0.0
    assert dash_cat_chain_indep > 0.29 and wa_l2_obs < (wa_l1_overall**3) and wa_l3_obs == 0.0

    # 5C: TheAgentCompany Table 1 (arXiv:2412.14161v3, p. 7) exact algebraic inversion of S_partial
    # S_partial = 0.5 * E[R/T] + 0.5 * S_full  ==>  E[R/T | S_full=0] = 2*(S_partial - S_full) / (1 - S_full)
    tac_leaderboard = [
        ("Gemini-2.5-Pro", 0.303, 0.393),
        ("Claude-3.7-Sonnet", 0.263, 0.364),
        ("Claude-3.5-Sonnet", 0.240, 0.344),
        ("Gemini-2.0-Flash", 0.114, 0.190),
        ("GPT-4o(OpenHands)", 0.086, 0.167),
        ("OWL-RolePlay", 0.040, 0.113),
        ("Qwen-2-72B", 0.011, 0.042),
    ]
    failed_ckpt_means: dict[str, float] = {}
    inflation_multipliers: dict[str, float] = {}
    for model, s_full, s_part in tac_leaderboard:
        mean_ckpt_on_fail = (2.0 * (s_part - s_full)) / (1.0 - s_full)
        failed_ckpt_means[model] = mean_ckpt_on_fail
        inflation_multipliers[model] = s_part / s_full
        assert 0.0 < mean_ckpt_on_fail < 0.30

    assert inflation_multipliers["GPT-4o(OpenHands)"] > 1.90
    assert inflation_multipliers["OWL-RolePlay"] > 2.80
    # Table 1 1-decimal-place rounded 4.2%/1.1% = 3.82x (exact 2/175 = 1.143% -> 3.68x):
    assert inflation_multipliers["Qwen-2-72B"] > 3.60

    print("PROBE 5 (Basis: documentation + derived + execution — horizon & variant-consistency laws)")
    print(
        f"  AppWorld Table 3 GPT-4o/GPT-4-Turbo (12- & 16-cell): TGC/SGC={min(ratios_all):.2f}x..{max(ratios_all):.2f}x,"
        f" rho in [{min(rhos_all):.3f}, {max(rhos_all):.3f}]"
        f" (6-cell subset: {min(ratios_6):.2f}x..{max(ratios_6):.2f}x, rho in [{min(rhos_6):.3f}, {max(rhos_6):.3f}];"
        f" GPT-4o+ReAct Test-N rho={by_name['GPT-4o+ReAct(Test-N)'][1]:.3f}, Test-C rho={by_name['GPT-4o+ReAct(Test-C)'][1]:.3f})"
    )
    print(
        f"  WorkArena L1->L2->L3 cliff: L1={wa_l1_overall*100:.1f}%, L1^3={wa_l1_overall**3*100:.2f}%,"
        f" Dash+Menu+Catalog indep={dash_cat_chain_indep*100:.2f}% vs observed L2={wa_l2_obs*100:.1f}%, L3={wa_l3_obs*100:.1f}%"
        f" (Filter-chain={offboard_chain_indep*100:.1f}%)"
    )
    print(
        "  TheAgentCompany failed-task partial-checkpoint residue E[R/T | S_full=0]:"
        f" Gemini-2.5-Pro={failed_ckpt_means['Gemini-2.5-Pro']*100:.1f}%,"
        f" GPT-4o={failed_ckpt_means['GPT-4o(OpenHands)']*100:.1f}% (S_partial/S_full={inflation_multipliers['GPT-4o(OpenHands)']:.2f}x),"
        f" OWL={failed_ckpt_means['OWL-RolePlay']*100:.1f}% ({inflation_multipliers['OWL-RolePlay']:.2f}x)"
    )
    return {
        "max_tgc_sgc_ratio": max(ratios_all),
        "owl_inflation": inflation_multipliers["OWL-RolePlay"],
    }


def main() -> int:
    if sys.version_info < (3, 10):
        raise SystemExit("Python 3.10+ required")
    print("=========================================================================")
    print("ENTERPRISE STATEFUL TOOL-USE, IDEMPOTENCY & SAGA VERIFICATION SUITE")
    print("=========================================================================")
    run_probe_1()
    print("-------------------------------------------------------------------------")
    run_probe_2()
    print("-------------------------------------------------------------------------")
    run_probe_3()
    print("-------------------------------------------------------------------------")
    run_probe_4()
    print("-------------------------------------------------------------------------")
    run_probe_5()
    print("=========================================================================")
    print("ALL 5 STATEFUL ENTERPRISE & SAGA PROBES PASSED NON-VACUOUS INVARIANTS.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
