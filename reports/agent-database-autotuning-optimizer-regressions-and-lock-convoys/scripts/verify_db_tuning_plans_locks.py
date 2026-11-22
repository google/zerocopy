#!/usr/bin/env python3
"""Deterministic executable verification suite for database tuning, query plans, and DDL locks.

Covers five primary-source verification pillars using only the Python 3.10+ standard library:
  1. Correlated multi-join cardinality underestimation (Leis et al., PVLDB 2015) and a live
     sqlite3 ANALYZE nested-loop vs. ephemeral covering B-tree + Bloom filter plan cliff,
     plus cost-constant calibration insensitivity under cardinality error.
  2. HypoPG (a0d0213d) synthetic B-tree page estimation, PostgreSQL (9b5d4e33) btcostestimate +
     genericcostestimate + Mackert-Lohmann index scan costing, and Dexter (da35df3a) 50%
     read-EXPLAIN gate failure modes (bloat undercutting, unclustered scan regression, and
     Heap-Only Tuple [HOT] write amplification) vs. two-sided read + write gating (Ding et al., 2019).
  3. Durability-knob admissibility audit across OtterTune (9758c657), DB-BERT (120a61c6), and
     GPTuner (89401e61), paired with deterministic factored UCB optimization across cloud-block
     vs. tmpfs flush regimes demonstrating ACID-violating reward hacking without hard locks.
  4. PostgreSQL (9b5d4e33) lock.c waitMask convoy cascade across a 100-connection pool and
     4-transaction indexcmds.c CREATE INDEX CONCURRENTLY (WaitForLockers vs. WaitForOlderSnapshots)
     indisvalid=false, indisready=true zombie index accumulation.
  5. Equal-column ORM N+1 lazy loading vs. IN-batching and 1-child/2-child LEFT JOIN row and
     VDBE instruction scaling, plus COUNT(*) vs. LIMIT 1 early termination (Yang et al., ICSE 2018).
"""

from __future__ import annotations

import dataclasses
import math
import re
import sqlite3


def count_vdbe_steps(conn: sqlite3.Connection, sql: str, params: tuple = ()) -> tuple[list[tuple], int]:
    """Execute SQL while counting exact deterministic SQLite VDBE virtual-machine instructions."""
    steps = 0

    def _progress() -> int:
        nonlocal steps
        steps += 1
        return 0

    conn.set_progress_handler(_progress, 1)
    try:
        rows = conn.execute(sql, params).fetchall()
    finally:
        conn.set_progress_handler(None, 0)
    return rows, steps


# ==============================================================================
# PROBE 1: Leis 2015 Correlated Multi-Join Cardinality Cliff & Cost Insensitivity
# ==============================================================================


def system_r_nl_cost(
    est_outer_rows: float,
    outer_scan_cost: float,
    inner_tree_height: int = 2,
    random_page_cost: float = 4.0,
    cpu_index_tuple_cost: float = 0.005,
    cpu_tuple_cost: float = 0.01,
    inner_cache_hit_ratio: float = 0.70,
) -> float:
    """Parameterized System-R / PostgreSQL Index Nested-Loop Join cost model."""
    effective_random_io = (1.0 - inner_cache_hit_ratio) * random_page_cost
    per_outer_probe = (
        (inner_tree_height + 1) * cpu_index_tuple_cost
        + effective_random_io
        + cpu_tuple_cost
    )
    return outer_scan_cost + est_outer_rows * per_outer_probe


def system_r_hash_join_cost(
    est_outer_rows: float,
    outer_scan_cost: float,
    inner_pages: int,
    inner_rows: int,
    seq_page_cost: float = 1.0,
    cpu_tuple_cost: float = 0.01,
    cpu_operator_cost: float = 0.0025,
) -> float:
    """Parameterized System-R / PostgreSQL in-memory Hash Join cost model."""
    inner_scan_and_build = inner_pages * seq_page_cost + inner_rows * (cpu_tuple_cost + cpu_operator_cost)
    probe_and_emit = est_outer_rows * (cpu_operator_cost + cpu_tuple_cost)
    return outer_scan_cost + inner_scan_and_build + probe_and_emit


def run_probe_1() -> None:
    print("=== PROBE 1: Correlated Multi-Join Cardinality Cliff & Cost-Constant Insensitivity ===")
    print("Provenance: [real sqlite3 execution + analytical optimizer model]")

    # Part 1A: Analytical System-R independence q-error across k=1..4 correlated joins
    n_entities = 10_000
    marginal_selectivity = 0.10
    true_cohort_rows = int(n_entities * marginal_selectivity)  # 1,000 exact co-occurring entities
    q_errors_by_join: list[tuple[int, float, int, float]] = []
    for k_joins in (1, 2, 3, 4):
        # k joins across (k + 1) tables, each carrying one correlated s = 0.10 predicate
        est_rows = n_entities * (marginal_selectivity ** (k_joins + 1))
        q_err = true_cohort_rows / est_rows
        q_errors_by_join.append((k_joins, est_rows, true_cohort_rows, q_err))

    assert abs(q_errors_by_join[0][3] - 10.0) < 1e-9
    assert abs(q_errors_by_join[3][3] - 10_000.0) < 1e-6

    # Part 1B: Real in-memory sqlite3 execution before and after ANALYZE (zero single-column skew)
    conn = sqlite3.connect(":memory:")
    conn.executescript(
        """
        CREATE TABLE titles (
            id INTEGER PRIMARY KEY,
            title_code INTEGER NOT NULL,
            g1 INTEGER NOT NULL,
            g2 INTEGER NOT NULL,
            g3 INTEGER NOT NULL,
            g4 INTEGER NOT NULL
        );
        CREATE INDEX idx_t_g1 ON titles(g1);

        CREATE TABLE title_tags (
            tid INTEGER NOT NULL,
            tag1 INTEGER NOT NULL,
            tag2 INTEGER NOT NULL,
            tag3 INTEGER NOT NULL
        );
        CREATE INDEX idx_tt_t1 ON title_tags(tag1);

        CREATE TABLE title_awards (
            tid INTEGER NOT NULL,
            aw1 INTEGER NOT NULL,
            aw2 INTEGER NOT NULL,
            aw3 INTEGER NOT NULL
        );
        CREATE INDEX idx_ta_a1 ON title_awards(aw1);

        CREATE TABLE box_office (
            bo_id INTEGER PRIMARY KEY,
            title_code INTEGER NOT NULL,
            region INTEGER NOT NULL,
            rev INTEGER NOT NULL
        );
        """
    )

    n_rows = 2_000
    cohort_size = 200  # 10 uniform cohorts of 200 rows -> exact s = 0.10, zero histogram skew
    conn.executemany(
        "INSERT INTO titles VALUES (?,?,?,?,?,?)",
        [(i, i + 100_000, i // cohort_size, i // cohort_size, i // cohort_size, i // cohort_size) for i in range(n_rows)],
    )
    conn.executemany(
        "INSERT INTO title_tags VALUES (?,?,?,?)",
        [(i, i // cohort_size, i // cohort_size, i // cohort_size) for i in range(n_rows)],
    )
    conn.executemany(
        "INSERT INTO title_awards VALUES (?,?,?,?)",
        [(i, i // cohort_size, i // cohort_size, i // cohort_size) for i in range(n_rows)],
    )
    conn.executemany(
        "INSERT INTO box_office VALUES (?,?,?,?)",
        [(i, i + 100_000, i % 5, (i * 17) % 1_000) for i in range(n_rows)],
    )

    sql_default_nl = """
        SELECT COUNT(*), SUM(bo.rev)
        FROM titles t
        JOIN title_tags tt ON tt.tid = t.id
        JOIN title_awards ta ON ta.tid = t.id
        JOIN box_office bo ON bo.title_code = t.title_code
        WHERE t.g1 = 1 AND t.g2 = 1 AND t.g3 = 1 AND t.g4 = 1
          AND tt.tag1 = 1 AND tt.tag2 = 1 AND tt.tag3 = 1
          AND ta.aw1 = 1 AND ta.aw2 = 1 AND ta.aw3 = 1
          AND bo.region = 2
    """
    plan_pre_analyze = [row[3] for row in conn.execute("EXPLAIN QUERY PLAN " + sql_default_nl).fetchall()]

    conn.execute("ANALYZE")
    stat1_rows = sorted(conn.execute("SELECT tbl, idx, stat FROM sqlite_stat1").fetchall())
    assert ("titles", "idx_t_g1", "2000 200") in stat1_rows
    assert ("title_tags", "idx_tt_t1", "2000 200") in stat1_rows
    assert ("title_awards", "idx_ta_a1", "2000 200") in stat1_rows

    # Unary '+' suppresses the secondary-index nested-loop scan on ta(aw1), forcing SQLite to build
    # an ephemeral covering B-tree + Bloom filter (OP_OpenEphemeral) over (aw2, aw3, tid).
    sql_forced_ephemeral_btree = sql_default_nl.replace("AND ta.aw1 = 1", "AND +ta.aw1 = 1")

    plan_nl = [row[3] for row in conn.execute("EXPLAIN QUERY PLAN " + sql_default_nl).fetchall()]
    plan_ephemeral_btree = [
        row[3] for row in conn.execute("EXPLAIN QUERY PLAN " + sql_forced_ephemeral_btree).fetchall()
    ]
    res_nl, vdbe_nl = count_vdbe_steps(conn, sql_default_nl)
    res_ephemeral_btree, vdbe_ephemeral_btree = count_vdbe_steps(conn, sql_forced_ephemeral_btree)
    conn.close()

    assert res_nl == res_ephemeral_btree == [(40, 20_660)]
    assert vdbe_nl == 413_937 and vdbe_ephemeral_btree == 24_137
    assert any("USING INDEX idx_ta_a1" in step for step in plan_pre_analyze)
    assert any("USING INDEX idx_ta_a1" in step for step in plan_nl)
    assert any("BLOOM FILTER ON ta" in step for step in plan_ephemeral_btree)
    assert any("AUTOMATIC PARTIAL COVERING INDEX" in step and "ta" in step for step in plan_ephemeral_btree)
    vdbe_slowdown = vdbe_nl / vdbe_ephemeral_btree
    assert vdbe_slowdown > 15.0

    # Part 1C: Leis 2015 Sec. 4 — tuning random_page_cost (4.0 -> 1.5) without fixing cardinalities
    inner_pages, inner_rows = 2_000, 100_000
    outer_scan = 250.0
    # Workload of 6 multi-join queries across sizes under 20x 2-join underestimation (cache hit = 0.25)
    true_outers = [5_000, 15_000, 25_000, 35_000, 50_000, 80_000]
    q_under = 20.0

    def eval_workload_cost(rpc_est: float, use_true_card: bool, true_rpc_hw: float = 1.5) -> tuple[float, int]:
        total_true_cost = 0.0
        nl_chosen = 0
        for r_true in true_outers:
            r_est = float(r_true) if use_true_card else (r_true / q_under)
            c_nl_est = system_r_nl_cost(
                r_est, outer_scan, random_page_cost=rpc_est, inner_cache_hit_ratio=0.25
            )
            c_hj_est = system_r_hash_join_cost(r_est, outer_scan, inner_pages, inner_rows)
            if c_nl_est < c_hj_est:
                nl_chosen += 1
                total_true_cost += system_r_nl_cost(
                    r_true, outer_scan, random_page_cost=true_rpc_hw, inner_cache_hit_ratio=0.25
                )
            else:
                total_true_cost += system_r_hash_join_cost(r_true, outer_scan, inner_pages, inner_rows)
        return total_true_cost, nl_chosen

    cost_default_under, nl_default_under = eval_workload_cost(rpc_est=4.0, use_true_card=False)
    cost_ssd_tuned_under, nl_ssd_tuned_under = eval_workload_cost(rpc_est=1.5, use_true_card=False)
    cost_uncalib_true_card, nl_true_card = eval_workload_cost(rpc_est=4.0, use_true_card=True)
    cost_optimal, _ = eval_workload_cost(rpc_est=1.5, use_true_card=True)

    # Lowering random_page_cost 4.0 -> 1.5 under 20x underestimation lures MORE queries into NLJ!
    assert nl_ssd_tuned_under > nl_default_under
    assert cost_ssd_tuned_under > cost_default_under * 1.15
    assert cost_uncalib_true_card <= cost_optimal * 1.05

    print(
        f"  [1A] Independence q-error by join depth (s=0.10, true=1000): "
        + ", ".join(f"k={k}: est={est:.2f} ({q:.0f}x)" for k, est, _, q in q_errors_by_join)
    )
    print(
        f"  [1B] Live sqlite3 3-join cliff persisting after ANALYZE (exact stat1='2000 200'): "
        f"NL_vdbe={vdbe_nl} vs ephemeral_btree_vdbe={vdbe_ephemeral_btree} ({vdbe_slowdown:.2f}x slowdown)"
    )
    print(
        f"  [1C] Cost-constant tuning vs true cardinalities (20x underest, SSD random_page_cost=1.5): "
        f"underest_rpc4.0={cost_default_under:.1f} (NL={nl_default_under}/6) -> "
        f"underest_rpc1.5={cost_ssd_tuned_under:.1f} (NL={nl_ssd_tuned_under}/6, {cost_ssd_tuned_under / cost_default_under:.2f}x WORSE) vs "
        f"true_card_rpc4.0={cost_uncalib_true_card:.1f} (NL={nl_true_card}/6)"
    )


# ==============================================================================
# PROBE 2: HypoPG (a0d0213d) + Dexter (da35df3a) Illusion vs Ding 2019 Gate
# ==============================================================================


def hypopg_estimate_btree_pages(
    tuples: float,
    ind_avg_width: int,
    fillfactor: int = 0,
    additional_bloat: int = 30,
) -> tuple[int, int]:
    """Exact port of hypo_estimate_index B-tree branch in HypoPG hypopg_index.c:2229-2241."""
    maxalign_index_tuple_data = 8  # MAXALIGN(sizeof(IndexTupleData)) on 64-bit PG
    sizeof_item_id_data = 4        # sizeof(ItemIdData)
    blcksz = 8192
    sizeof_page_header_data = 24
    sizeof_bt_page_opaque_data = 16

    line_size = ind_avg_width + maxalign_index_tuple_data + sizeof_item_id_data
    usable_page_size = blcksz - sizeof_page_header_data - sizeof_bt_page_opaque_data
    if fillfactor == 0:
        fillfactor = 90  # BTREE_DEFAULT_FILLFACTOR
    bloat_factor = (100.0 + additional_bloat) / fillfactor  # 130.0 / 90.0 = 1.4444...
    pages = int(tuples * line_size * bloat_factor / usable_page_size)
    tree_height = -1  # hypopg_index.c:2241: entry->tree_height = -1; /* TODO */
    return pages, tree_height


def dexter_accepts_single_col_index(
    initial_cost: float,
    new_cost: float,
    min_cost: int = 100,
    min_cost_savings_pct: int = 50,
) -> bool:
    """Exact port of Dexter single-column cost gate (lib/dexter/client.rb:88-89, indexer.rb:286-292)."""
    if initial_cost < min_cost:
        return False
    savings_ratio = 1.0 - (min_cost_savings_pct / 100.0)
    return new_cost < initial_cost * savings_ratio


def mackert_lohmann_pages_fetched(
    tuples_fetched: float,
    heap_pages: int,
    effective_cache_pages: int = 524_288,
) -> float:
    """Port of PostgreSQL index_pages_fetched (src/backend/optimizer/path/costsize.c:901-946)."""
    total_pages = float(heap_pages)
    cache_pages = float(effective_cache_pages)
    if total_pages <= 1.0:
        return min(total_pages, tuples_fetched)
    if total_pages <= cache_pages:
        pages = (2.0 * total_pages * tuples_fetched) / (2.0 * total_pages + tuples_fetched)
        return min(total_pages, float(math.ceil(pages)))
    lim = (2.0 * total_pages * cache_pages) / (2.0 * total_pages - cache_pages)
    if tuples_fetched <= lim:
        pages = (2.0 * total_pages * tuples_fetched) / (2.0 * total_pages + tuples_fetched)
    else:
        pages = cache_pages + (tuples_fetched - lim) * (total_pages - cache_pages) / total_pages
    return min(total_pages, float(math.ceil(pages)))


def pg_bt_index_scan_cost(
    heap_pages: int,
    heap_tuples: int,
    index_pages: int,
    selectivity: float,
    correlation: float,
    tree_height: int,
    random_page_cost: float = 4.0,
    seq_page_cost: float = 1.0,
    cpu_tuple_cost: float = 0.01,
    cpu_index_tuple_cost: float = 0.005,
    cpu_operator_cost: float = 0.0025,
) -> float:
    """Single-scan PostgreSQL btcostestimate + genericcostestimate + cost_index model.

    Mirrors postgres@9b5d4e33:
      - selfuncs.c:8201: descent CPU = (index->tree_height + 1) * 50.0 * cpu_operator_cost
        (evaluates to 0.0 when HypoPG leaves entry->tree_height == -1).
      - selfuncs.c:7622: single-scan index leaf I/O = ceil(tuples_fetched * index_pages / tuples)
        charged at full 1.0 * spc_random_page_cost.
      - costsize.c:615-715, 928: correlation^2 interpolation between Mackert-Lohmann random page
        fetches and clustered sequential heap page fetches.
    """
    tuples_fetched = max(1.0, float(round(heap_tuples * selectivity)))
    descent_cpu = (tree_height + 1) * 50.0 * cpu_operator_cost
    num_index_pages = math.ceil(tuples_fetched * index_pages / max(1.0, float(heap_tuples)))
    index_io = num_index_pages * random_page_cost
    index_cpu = descent_cpu + tuples_fetched * (cpu_index_tuple_cost + cpu_operator_cost)

    max_io_pages = mackert_lohmann_pages_fetched(tuples_fetched, heap_pages)
    min_io_pages = mackert_lohmann_pages_fetched(1.0, heap_pages) + math.floor(selectivity * heap_pages)
    corr2 = correlation * correlation
    max_io_cost = max_io_pages * random_page_cost
    min_io_cost = 1.0 * random_page_cost + max(0.0, min_io_pages - 1.0) * seq_page_cost
    heap_io = corr2 * min_io_cost + (1.0 - corr2) * max_io_cost
    heap_cpu = tuples_fetched * cpu_tuple_cost
    return index_io + index_cpu + heap_io + heap_cpu


def run_probe_2() -> None:
    print("\n=== PROBE 2: HypoPG + Dexter What-If Cost Illusion & HOT Write Amplification ===")
    print("Provenance: [exact reproduction of pinned repository logic] + [derived analytical model]")

    # Part 2A: HypoPG synthetic bloat (130/90 = 1.444x, tree_height=-1) vs bloated live B-tree
    n_million = 1_000_000
    hypo_pages, hypo_height = hypopg_estimate_btree_pages(n_million, ind_avg_width=8)
    packed_100pct_leaf_pages = math.ceil(n_million * (8 + 12) / 8152)          # 2,454 pages at 100% packing
    ff90_fresh_leaf_pages = math.ceil(n_million * (8 + 12) / (8152 * 0.90))    # 2,726 leaf pages at fillfactor=90
    live_bloated_pages = int(packed_100pct_leaf_pages * 2.40)                  # 5,889 pages after post-churn splits

    cost_using_live_btree = pg_bt_index_scan_cost(
        heap_pages=25_000,
        heap_tuples=n_million,
        index_pages=live_bloated_pages,
        selectivity=0.01,
        correlation=0.85,
        tree_height=3,
    )
    cost_using_duplicate_hypo = pg_bt_index_scan_cost(
        heap_pages=25_000,
        heap_tuples=n_million,
        index_pages=hypo_pages,
        selectivity=0.01,
        correlation=0.85,
        tree_height=hypo_height,
    )
    assert packed_100pct_leaf_pages == 2_454 and ff90_fresh_leaf_pages == 2_726
    assert hypo_pages == 3_543 and hypo_height == -1 and live_bloated_pages == 5_889
    assert cost_using_duplicate_hypo < cost_using_live_btree

    # Part 2B: Unclustered heap scan + multi-predicate/expression underestimation passing Dexter's 50% bar
    heap_pages, heap_tuples = 2_500, 100_000
    seq_scan_cost = heap_pages * 1.0 + heap_tuples * (0.01 + 0.0025)  # 3,750.0
    cand_hypo_pages, cand_height = hypopg_estimate_btree_pages(heap_tuples, ind_avg_width=8)

    whatif_est_cost = pg_bt_index_scan_cost(
        heap_pages, heap_tuples, cand_hypo_pages, selectivity=0.002, correlation=0.02, tree_height=cand_height
    )
    true_exec_index_cost = pg_bt_index_scan_cost(
        heap_pages, heap_tuples, cand_hypo_pages, selectivity=0.06, correlation=0.02, tree_height=2
    )
    dexter_recommends_bad_read_idx = dexter_accepts_single_col_index(seq_scan_cost, whatif_est_cost)
    read_regression_ratio = true_exec_index_cost / seq_scan_cost
    assert dexter_recommends_bad_read_idx is True
    assert read_regression_ratio > 2.5

    # Part 2C: Transparent OLTP Heap-Only Tuple (HOT) page-cost accounting (zero scaling fudge factors)
    # Active 200-page (10,000-row, fillfactor=80) OLTP status table with K=4 immutable-key indexes.
    oltp_pages, oltp_tuples = 200, 10_000
    existing_indexes = 4
    hot_ratio_before = 0.95  # fillfactor=80 allows 95% in-page HOT updates -> 0 index writes
    hot_ratio_after = 0.00   # indexing status_code sets rd_hotblockingattr -> 0% HOT on status updates

    read_cost_before = oltp_pages * 1.0 + oltp_tuples * (0.01 + 0.0025)  # 325.0 (>= Dexter min_cost=100)
    oltp_hypo_pages, oltp_hypo_height = hypopg_estimate_btree_pages(oltp_tuples, ind_avg_width=8)
    read_cost_after = pg_bt_index_scan_cost(
        oltp_pages, oltp_tuples, oltp_hypo_pages, selectivity=0.002, correlation=0.10, tree_height=oltp_hypo_height
    )
    dexter_recommends_hot_killer = dexter_accepts_single_col_index(read_cost_before, read_cost_after)

    # Commensurate PostgreSQL page-cost units (seq_page_cost=1.0, random_page_cost=4.0):
    #   - In-page heap tuple modification + WAL record: 1.0 * random_page_cost = 4.0
    #   - Non-HOT overflow heap page pin/modify:        1.0 * random_page_cost = 4.0
    #   - Per-index B-tree leaf fetch (4.0) + dirty leaf writeback / WAL XLOG_BTREE_INSERT_LEAF (4.0): 8.0
    inpage_heap_cost = 4.0
    overflow_heap_cost = 4.0
    per_index_insert_cost = 8.0

    upd_cost_before = inpage_heap_cost + (1.0 - hot_ratio_before) * (
        overflow_heap_cost + existing_indexes * per_index_insert_cost
    )  # 5.80
    upd_cost_hot_broken = inpage_heap_cost + (1.0 - hot_ratio_after) * (
        overflow_heap_cost + (existing_indexes + 1) * per_index_insert_cost
    )  # 48.00 (8.28x per-UPDATE write amplification)
    upd_cost_hot_safe = inpage_heap_cost + (1.0 - hot_ratio_before) * (
        overflow_heap_cost + (existing_indexes + 1) * per_index_insert_cost
    )  # 6.20 (HOT preserved at 0.95 when indexing an immutable filter column)

    # Exact closed-form UPDATE:SELECT crossover ratio R* where net workload delta = 0
    read_savings = read_cost_before - read_cost_after
    crossover_r_hot_broken = read_savings / (upd_cost_hot_broken - upd_cost_before)
    crossover_r_hot_safe = read_savings / (upd_cost_hot_safe - upd_cost_before)

    # Evaluate on a state-machine / job-queue OLTP mix: 50 SELECT/s + 2,000 UPDATE/s (R = 40:1)
    select_rate, update_rate = 50.0, 2_000.0
    total_wl_before = select_rate * read_cost_before + update_rate * upd_cost_before
    total_wl_hot_broken = select_rate * read_cost_after + update_rate * upd_cost_hot_broken
    total_wl_hot_safe = select_rate * read_cost_after + update_rate * upd_cost_hot_safe
    oltp_net_regression = total_wl_hot_broken / total_wl_before
    oltp_safe_speedup = total_wl_before / total_wl_hot_safe

    def ding2019_and_write_gate(
        w_before: float,
        w_after: float,
        per_query_true_ratios: list[float],
        lambda_tol: float = 0.20,
    ) -> bool:
        """Two-sided workload + execution-verified per-query regression gate (Ding et al., SIGMOD 2019)."""
        if any(r > (1.0 + lambda_tol) for r in per_query_true_ratios):
            return False
        return w_after < w_before * 0.90

    gate_accepts_bad_read = ding2019_and_write_gate(seq_scan_cost, true_exec_index_cost, [read_regression_ratio])
    gate_accepts_hot_killer = ding2019_and_write_gate(
        total_wl_before, total_wl_hot_broken, [read_cost_after / read_cost_before]
    )
    gate_accepts_safe_idx = ding2019_and_write_gate(
        total_wl_before, total_wl_hot_safe, [read_cost_after / read_cost_before]
    )

    assert dexter_recommends_hot_killer is True
    assert abs(upd_cost_before - 5.80) < 1e-9 and abs(upd_cost_hot_broken - 48.00) < 1e-9
    assert 5.0 < crossover_r_hot_broken < 6.5 and crossover_r_hot_safe > 500.0
    assert oltp_net_regression > 3.5 and oltp_safe_speedup > 1.6
    assert gate_accepts_bad_read is False
    assert gate_accepts_hot_killer is False
    assert gate_accepts_safe_idx is True

    print(
        f"  [2A] HypoPG 1M-row int8 bloat illusion: packed100={packed_100pct_leaf_pages}, ff90={ff90_fresh_leaf_pages}, "
        f"hypo_pages={hypo_pages} (tree_height={hypo_height}) vs live_2.4x={live_bloated_pages} -> "
        f"hypo_cost={cost_using_duplicate_hypo:.2f} < live_cost={cost_using_live_btree:.2f} (delta={cost_using_live_btree - cost_using_duplicate_hypo:.2f})"
    )
    print(
        f"  [2B] Unclustered scan cliff: seq_cost={seq_scan_cost:.1f}, whatif_est={whatif_est_cost:.2f} "
        f"(Dexter_accept={dexter_recommends_bad_read_idx}), true_exec={true_exec_index_cost:.2f} ({read_regression_ratio:.2f}x regression)"
    )
    print(
        f"  [2C] HOT-update invalidation (K=4 indexes, read {read_cost_before:.1f}->{read_cost_after:.2f}, "
        f"upd {upd_cost_before:.2f}->{upd_cost_hot_broken:.2f} vs safe {upd_cost_hot_safe:.2f}): "
        f"R*_broken={crossover_r_hot_broken:.2f} upd/sel (vs R*_safe={crossover_r_hot_safe:.1f}); "
        f"at R=40:1 (50 sel/s, 2000 upd/s) Dexter_accept={dexter_recommends_hot_killer}, "
        f"net_ratio={oltp_net_regression:.2f}x WORSE (safe={oltp_safe_speedup:.2f}x speedup) | "
        f"Ding+Write gate: bad_read={gate_accepts_bad_read}, hot_killer={gate_accepts_hot_killer}, safe={gate_accepts_safe_idx}"
    )


# ==============================================================================
# PROBE 3: Durability-Knob Admissibility Audit & BO Reward-Hacking Simulation
# ==============================================================================


@dataclasses.dataclass(frozen=True)
class DurabilityKnobSpec:
    dbms: str
    name: str
    vartype_in_gptuner_sysview: str | None
    default_str_in_dbms: str
    in_gptuner_default_target_txt: bool
    gptuner_cli_candidate_status: str  # "missing_file" | "invalid_json_and_omitted"
    ottertune_tunable: bool
    unsafe_numeric_token: str | None


DURABILITY_KNOBS: tuple[DurabilityKnobSpec, ...] = (
    DurabilityKnobSpec("postgres", "fsync", "bool", "on", False, "invalid_json_and_omitted", False, "0"),
    DurabilityKnobSpec("postgres", "synchronous_commit", "enum", "on", False, "invalid_json_and_omitted", False, "0"),
    DurabilityKnobSpec("postgres", "full_page_writes", "bool", "on", False, "invalid_json_and_omitted", False, "0"),
    DurabilityKnobSpec("mysql", "innodb_flush_log_at_trx_commit", "enum", "1", False, "missing_file", False, "0"),
    DurabilityKnobSpec("mysql", "innodb_doublewrite", None, "ON", False, "missing_file", False, "0"),
    DurabilityKnobSpec("mysql", "sync_binlog", "integer", "1", False, "missing_file", False, "0"),
)


def audit_repo_durability_exposure() -> dict[str, list[str]]:
    """Exact reproduction of pinned durability-knob admissibility rules across 3 autotuners."""
    # DB-BERT (120a61c6): src/parameters/util.py:9-14 (param_reg, value_reg, is_numerical)
    dbbert_param_re = re.compile(r"[a-z_]+_[a-z]+$")
    dbbert_val_re = re.compile(r"(\d+(\.\d+)?)(%|\w*)$")

    ottertune_exposed: list[str] = []
    dbbert_nlp_exposed: list[str] = []
    dbbert_ddpg_exposed: list[str] = []
    gptuner_shipped_txt_exposed: list[str] = []
    gptuner_cli_missing_txt_exposed: list[str] = []
    gptuner_sysview_or_interdep_exposed: list[str] = []

    for k in DURABILITY_KNOBS:
        fq = f"{k.dbms}.{k.name}"
        # 1. OtterTune (9758c657): postgres-96_knobs.json & mysql-56_knobs.json curated tunable=False
        if k.ottertune_tunable:
            ottertune_exposed.append(fq)

        # 2a. DB-BERT NLP hint pipeline (doc/collection.py:185, 228-237 + postgres.py:136 / mysql.py:32,168):
        # Even when use_implicit appends PgConfig.all_params(), collection.py:228 re-filters exp_passage
        # through param_reg (r'[a-z_]+_[a-z]+'), rejecting underscore-less 'fsync'.
        name_ok = bool(dbbert_param_re.match(k.name))
        val_ok = k.unsafe_numeric_token is not None and bool(dbbert_val_re.match(k.unsafe_numeric_token))
        dbms_accepts = True if k.dbms == "postgres" else bool(dbbert_val_re.match(k.default_str_in_dbms))
        if name_ok and val_ok and dbms_accepts:
            dbbert_nlp_exposed.append(fq)

        # 2b. DB-BERT DDPG baselines (baselines/ddpg.py:129-130 & run/run_ddpg.py:162-163):
        # Both callers filter all_params() via is_numerical(dbms.get_value(p)); SHOW fsync / SHOW
        # full_page_writes return 'on', which fails is_numerical('on') == False!
        in_all_params = (
            k.vartype_in_gptuner_sysview in ("bool", "integer", "real")
            if k.dbms == "postgres"
            else bool(dbbert_val_re.match(k.default_str_in_dbms))
        )
        if in_all_params and bool(dbbert_val_re.match(k.default_str_in_dbms)):
            dbbert_ddpg_exposed.append(fq)

        # 3. GPTuner (89401e61):
        #   - Shipped target_knobs.txt (44 MySQL / 57 PG): omits all 6 durability knobs (0/6).
        #   - CLI space_optimizer/knob_selection.py:21-34 when target_knobs.txt is absent: crashes on
        #     missing mysql/candidate_knobs.txt (FileNotFoundError) and plain-text postgres/candidate_knobs.txt
        #     (JSONDecodeError, which also omits fsync, synchronous_commit, full_page_writes) -> 0/6.
        #   - Streamlit demo/util/get_knobs.py:11-23 (reading knob_info/system_view.json directly) or
        #     knob_selection.py:160-188 unconstrained GPT interdependent expansion into DefaultSpace/CoarseSpace:
        #     exposes 5/6 (blocking only mysql.innodb_doublewrite via missing 'vartype' & is_numerical('ON')).
        passes_space_and_setter = (
            k.vartype_in_gptuner_sysview is not None
            and k.vartype_in_gptuner_sysview != "string"
            and (k.dbms == "postgres" or bool(dbbert_val_re.match(k.default_str_in_dbms)))
        )
        if k.in_gptuner_default_target_txt and passes_space_and_setter:
            gptuner_shipped_txt_exposed.append(fq)
        if k.gptuner_cli_candidate_status == "valid_json_present" and passes_space_and_setter:
            gptuner_cli_missing_txt_exposed.append(fq)
        if passes_space_and_setter:
            gptuner_sysview_or_interdep_exposed.append(fq)

    return {
        "ottertune_curated": ottertune_exposed,
        "dbbert_nlp_hints": dbbert_nlp_exposed,
        "dbbert_ddpg": dbbert_ddpg_exposed,
        "dbbert_union": sorted(set(dbbert_nlp_exposed) | set(dbbert_ddpg_exposed)),
        "gptuner_shipped_target_txt": gptuner_shipped_txt_exposed,
        "gptuner_cli_unpatched_missing_txt": gptuner_cli_missing_txt_exposed,
        "gptuner_sysview_demo_or_interdep": gptuner_sysview_or_interdep_exposed,
    }


def oltp_throughput_and_durability(
    buffer_gb: float,
    work_mem_mb: float,
    sync_commit_on: bool,
    full_page_guard_on: bool,
    fdatasync_ms: float,
) -> tuple[float, float]:
    """Queue-free closed-loop Little's Law OLTP throughput (16 parallel streams) and crash safety."""
    # Working set 12 GB: larger buffer pool reduces random read misses exponentially
    cache_miss_prob = math.exp(-buffer_gb / 4.0)
    exec_cpu_and_read_ms = 0.22 + 1.40 * cache_miss_prob + (0.06 if work_mem_mb < 16.0 else 0.01)
    wal_flush_ms = (0.001 + fdatasync_ms) if sync_commit_on else 0.001
    doublewrite_overhead_ms = (0.28 * fdatasync_ms) if full_page_guard_on else 0.0
    mean_tx_latency_ms = exec_cpu_and_read_ms + wal_flush_ms + doublewrite_overhead_ms
    n_streams = 16.0
    tps = (n_streams * 1_000.0) / mean_tx_latency_ms
    # Crash safety: 1.0 iff both WAL commit flush and torn-page protection remain enabled
    crash_safe_fraction = 1.0 if (sync_commit_on and full_page_guard_on) else 0.0
    return tps, crash_safe_fraction


def run_ucb_knob_tuner(
    acid_locked: bool,
    fdatasync_ms: float,
    n_trials: int = 24,
) -> tuple[dict[str, object], float, float, int]:
    """Deterministic factored UCB bandit optimizer over discrete DBMS configuration arms."""
    arms: list[dict[str, object]] = []
    for buf_gb in (0.5, 2.0, 6.0, 10.0):
        for wmem_mb in (4.0, 32.0):
            sync_opts = (True,) if acid_locked else (True, False)
            fpw_opts = (True,) if acid_locked else (True, False)
            for sc in sync_opts:
                for fpw in fpw_opts:
                    arms.append(
                        {
                            "buffer_gb": buf_gb,
                            "work_mem_mb": wmem_mb,
                            "sync_commit": sc,
                            "full_page_guard": fpw,
                        }
                    )

    feat_counts: dict[tuple[str, object], int] = {}
    feat_sums: dict[tuple[str, object], float] = {}
    evaluated: set[int] = set()
    best_cfg = arms[0]
    best_tps = -1.0
    best_safety = 1.0
    first_unsafe_trial = -1

    for t in range(1, n_trials + 1):
        if t == 1:
            choice = 0
        else:
            best_score = -1e18
            choice = 0
            for idx, arm in enumerate(arms):
                if idx in evaluated:
                    continue
                pred = 0.0
                bonus = 0.0
                for k_name, k_val in sorted(arm.items()):
                    cnt = feat_counts.get((k_name, k_val), 0)
                    if cnt == 0:
                        pred += 4_000.0
                        bonus += 8_000.0
                    else:
                        pred += feat_sums[(k_name, k_val)] / cnt
                        bonus += 1_500.0 * math.sqrt(math.log(t + 1.0) / cnt)
                score = pred / 4.0 + bonus / 4.0
                if score > best_score:
                    best_score = score
                    choice = idx

        evaluated.add(choice)
        cfg = arms[choice]
        tps, safe = oltp_throughput_and_durability(
            float(cfg["buffer_gb"]),
            float(cfg["work_mem_mb"]),
            bool(cfg["sync_commit"]),
            bool(cfg["full_page_guard"]),
            fdatasync_ms=fdatasync_ms,
        )
        if safe < 1.0 and first_unsafe_trial < 0:
            first_unsafe_trial = t
        for k_name, k_val in sorted(cfg.items()):
            feat_counts[(k_name, k_val)] = feat_counts.get((k_name, k_val), 0) + 1
            feat_sums[(k_name, k_val)] = feat_sums.get((k_name, k_val), 0.0) + tps
        if tps > best_tps:
            best_tps = tps
            best_cfg = cfg
            best_safety = safe

    return best_cfg, best_tps, best_safety, first_unsafe_trial


def run_probe_3() -> None:
    print("\n=== PROBE 3: Durability-Knob Admissibility Audit & BO Reward-Hacking ===")
    print("Provenance: [exact reproduction of pinned repository logic] + [controlled simulation]")

    exposure = audit_repo_durability_exposure()
    assert len(exposure["ottertune_curated"]) == 0
    # DB-BERT:postgres.fsync is blocked across EVERY code path (param_reg requires '_' in NLP/use_implicit;
    # ddpg.py:130 / run_ddpg.py:163 filter is_numerical('on') == False), yielding 4/6 NLP, 2/6 DDPG, 4/6 union!
    assert len(exposure["dbbert_nlp_hints"]) == 4
    assert len(exposure["dbbert_ddpg"]) == 2
    assert len(exposure["dbbert_union"]) == 4
    assert "postgres.fsync" not in exposure["dbbert_nlp_hints"]
    assert "postgres.fsync" not in exposure["dbbert_union"]
    assert "mysql.innodb_doublewrite" not in exposure["dbbert_union"]
    # GPTuner: 0/6 in shipped target_knobs.txt, 0/6 (error) in unpatched CLI missing target_knobs.txt,
    # and 5/6 via Streamlit demo/util/get_knobs.py:11-23 (system_view.json) or knob_selection.py:160-188.
    assert len(exposure["gptuner_shipped_target_txt"]) == 0
    assert len(exposure["gptuner_cli_unpatched_missing_txt"]) == 0
    assert len(exposure["gptuner_sysview_demo_or_interdep"]) == 5
    assert "mysql.innodb_doublewrite" not in exposure["gptuner_sysview_demo_or_interdep"]

    default_cloud_tps, _ = oltp_throughput_and_durability(0.5, 4.0, True, True, fdatasync_ms=1.2)
    _, unguarded_tps, unguarded_safe, unsafe_step = run_ucb_knob_tuner(
        acid_locked=False, fdatasync_ms=1.2, n_trials=16
    )
    _, guarded_tps, guarded_safe, _ = run_ucb_knob_tuner(
        acid_locked=True, fdatasync_ms=1.2, n_trials=8
    )

    # CI tmpfs masking check (0.005 ms flush hides durability penalty)
    tmpfs_safe_tps, _ = oltp_throughput_and_durability(10.0, 32.0, True, True, fdatasync_ms=0.005)
    tmpfs_unsafe_tps, _ = oltp_throughput_and_durability(10.0, 32.0, False, False, fdatasync_ms=0.005)
    tmpfs_illusory_gain = tmpfs_unsafe_tps / tmpfs_safe_tps

    assert unguarded_safe == 0.0 and unsafe_step == 2
    assert guarded_safe == 1.0 and guarded_tps > default_cloud_tps * 1.45
    assert unguarded_tps > guarded_tps * 3.5
    assert tmpfs_illusory_gain < 1.08

    print(
        f"  [3A] Pinned durability-knob exposure (/6 knobs): "
        f"OtterTune={len(exposure['ottertune_curated'])}/6, "
        f"DB-BERT(NLP={len(exposure['dbbert_nlp_hints'])}/6, DDPG={len(exposure['dbbert_ddpg'])}/6, union={len(exposure['dbbert_union'])}/6), "
        f"GPTuner(shipped_txt={len(exposure['gptuner_shipped_target_txt'])}/6, cli_missing_txt_err={len(exposure['gptuner_cli_unpatched_missing_txt'])}/6, "
        f"sysview_demo_or_interdep={len(exposure['gptuner_sysview_demo_or_interdep'])}/6)"
    )
    print(
        f"  [3B] Cloud-block OLTP tuning (1.2ms fdatasync, 16-stream Little's Law, default={default_cloud_tps:.0f} tx/s): "
        f"unguarded_UCB={unguarded_tps:.0f} tx/s (ACID_safe={unguarded_safe:.0f}, first_unsafe_trial={unsafe_step}) vs "
        f"ACID_locked_UCB={guarded_tps:.0f} tx/s ({guarded_tps / default_cloud_tps:.2f}x safe speedup, ACID_safe={guarded_safe:.0f})"
    )
    print(
        f"  [3C] CI tmpfs masking (0.005ms fdatasync at tuned RAM): "
        f"unsafe/safe ratio={tmpfs_illusory_gain:.3f}x (<8% delta masks reward hack in container CI)"
    )


# ==============================================================================
# PROBE 4: PostgreSQL (9b5d4e33) lock.c:1140 Convoy & CONCURRENTLY Zombie Index
# ==============================================================================

ACCESS_SHARE = 1
ROW_SHARE = 2
ROW_EXCLUSIVE = 3
SHARE_UPDATE_EXCLUSIVE = 4
SHARE = 5
SHARE_ROW_EXCLUSIVE = 6
EXCLUSIVE = 7
ACCESS_EXCLUSIVE = 8


def _bit(mode: int) -> int:
    return 1 << mode


# Exact port of LockConflicts[] in postgres/postgres src/backend/storage/lmgr/lock.c:68-108
PG_CONFLICT_TAB: dict[int, int] = {
    ACCESS_SHARE: _bit(ACCESS_EXCLUSIVE),
    ROW_SHARE: _bit(EXCLUSIVE) | _bit(ACCESS_EXCLUSIVE),
    ROW_EXCLUSIVE: _bit(SHARE) | _bit(SHARE_ROW_EXCLUSIVE) | _bit(EXCLUSIVE) | _bit(ACCESS_EXCLUSIVE),
    SHARE_UPDATE_EXCLUSIVE: (
        _bit(SHARE_UPDATE_EXCLUSIVE)
        | _bit(SHARE)
        | _bit(SHARE_ROW_EXCLUSIVE)
        | _bit(EXCLUSIVE)
        | _bit(ACCESS_EXCLUSIVE)
    ),
    SHARE: (
        _bit(ROW_EXCLUSIVE)
        | _bit(SHARE_UPDATE_EXCLUSIVE)
        | _bit(SHARE_ROW_EXCLUSIVE)
        | _bit(EXCLUSIVE)
        | _bit(ACCESS_EXCLUSIVE)
    ),
    SHARE_ROW_EXCLUSIVE: (
        _bit(ROW_EXCLUSIVE)
        | _bit(SHARE_UPDATE_EXCLUSIVE)
        | _bit(SHARE)
        | _bit(SHARE_ROW_EXCLUSIVE)
        | _bit(EXCLUSIVE)
        | _bit(ACCESS_EXCLUSIVE)
    ),
    EXCLUSIVE: (
        _bit(ROW_SHARE)
        | _bit(ROW_EXCLUSIVE)
        | _bit(SHARE_UPDATE_EXCLUSIVE)
        | _bit(SHARE)
        | _bit(SHARE_ROW_EXCLUSIVE)
        | _bit(EXCLUSIVE)
        | _bit(ACCESS_EXCLUSIVE)
    ),
    ACCESS_EXCLUSIVE: (
        _bit(ACCESS_SHARE)
        | _bit(ROW_SHARE)
        | _bit(ROW_EXCLUSIVE)
        | _bit(SHARE_UPDATE_EXCLUSIVE)
        | _bit(SHARE)
        | _bit(SHARE_ROW_EXCLUSIVE)
        | _bit(EXCLUSIVE)
        | _bit(ACCESS_EXCLUSIVE)
    ),
}


def pg_lock_can_grant_immediately(req_mode: int, held_mask: int, wait_mask: int) -> bool:
    """Exact port of LockAcquireExtended conflict check (postgres lock.c:1140-1145)."""
    if PG_CONFLICT_TAB[req_mode] & wait_mask:
        return False
    if PG_CONFLICT_TAB[req_mode] & held_mask:
        return False
    return True


@dataclasses.dataclass
class LockConvoyResult:
    strategy: str
    pool_exhausted_at_s: float | None
    queued_selects: int
    rejected_selects: int
    queued_updates: int
    rejected_updates: int
    zombie_invalid_count: int
    zombie_indisready_write_amp: bool
    autovacuum_blocked: bool

    @property
    def disrupted_selects(self) -> int:
        return self.queued_selects + self.rejected_selects

    @property
    def disrupted_updates(self) -> int:
        return self.queued_updates + self.rejected_updates


def simulate_pg_ddl_strategy(
    strategy: str,
    long_holder_mode: int,
    long_holder_duration_s: float = 12.0,
    ddl_arrival_s: float = 0.50,
    pool_limit: int = 100,
    dexter_retry_runs: int = 1,
) -> LockConvoyResult:
    """Discrete-event simulation (10ms tick) of capped 100-conn pool + 4-tx indexcmds.c CIC phases."""
    dt = 0.010
    total_ticks = 1_400 if dexter_retry_runs == 1 else 20_000
    ddl_tick = int(round(ddl_arrival_s / dt))
    long_end_tick = int(round(long_holder_duration_s / dt))

    if strategy == "guarded_cic_preflight_cleanup":
        ddl_tick = long_end_tick + 1

    active_holders: list[tuple[int, int]] = [(long_holder_mode, long_end_tick)]
    wait_queue: list[tuple[str, int, int]] = []

    queued_selects = 0
    rejected_selects = 0
    queued_updates = 0
    rejected_updates = 0
    pool_exhausted_at_s: float | None = None
    zombie_invalid_count = 0
    zombie_indisready = False
    autovacuum_blocked = False

    # 4-transaction CIC state machine (indexcmds.c:1670, 1742, 1802, 1821-1832):
    #   tx1_committed -> Phase 1 (Tx2: WaitForLockers ShareLock + Scan 1 + commit indisready=true)
    #   -> Phase 2 (Tx3: WaitForLockers ShareLock + validate_index + commit clearing MyProc->xmin)
    #   -> Phase 3 (Tx4: WaitForOlderSnapshots via VirtualXactLock + INDEX_CREATE_SET_VALID).
    # Note: PostgreSQL's lock_timeout bounds EACH individual lock wait, not cumulative scan time.
    cic_tx_phase = 0
    cic_wait_started_tick = 0
    per_wait_timeout_ticks = 500  # SET lock_timeout = '5s' per individual barrier wait
    scheduled_cic_starts = [ddl_tick + r * 6_000 for r in range(dexter_retry_runs)]

    for tick in range(total_ticks):
        active_holders = [(m, rel) for (m, rel) in active_holders if rel > tick]

        if tick in scheduled_cic_starts:
            if strategy == "alter_table_access_exclusive":
                wait_queue.append(("ddl", ACCESS_EXCLUSIVE, 999_999))
            elif strategy == "create_index_share_lock":
                wait_queue.append(("ddl", SHARE, 999_999))
            elif strategy in ("dexter_cic_5s_timeout", "guarded_cic_preflight_cleanup"):
                # Tx1 (indexcmds.c:1667, 1670): acquire session ShareUpdateExclusiveLock & commit
                # pg_index catalog row (indisvalid=false, indisready=false). Dexter's indexer.rb:521
                # queries WHERE indisvalid = 't', ignoring prior invalid residue on subsequent 60s runs!
                active_holders.append((SHARE_UPDATE_EXCLUSIVE, tick + 600))
                cic_tx_phase = 1
                cic_wait_started_tick = tick

        if cic_tx_phase in (1, 2, 3):
            held_mask_now = 0
            for m, _ in active_holders:
                held_mask_now |= _bit(m)
            if PG_CONFLICT_TAB[SHARE_UPDATE_EXCLUSIVE] & held_mask_now:
                autovacuum_blocked = True

            writer_conflict = any(
                (PG_CONFLICT_TAB[SHARE] & _bit(m)) != 0 and rel == long_end_tick
                for (m, rel) in active_holders
            )
            older_snapshot_alive = tick < long_end_tick

            if cic_tx_phase == 1 and not writer_conflict:
                # Tx2 commits indisready=true (indexcmds.c:1742); enter Tx3 WAIT_2
                cic_tx_phase = 2
                cic_wait_started_tick = tick
            if cic_tx_phase == 2 and not writer_conflict:
                # Tx3 commits validate_index & clears MyProc->xmin (indexcmds.c:1802); enter Tx4 WAIT_3
                cic_tx_phase = 3
                cic_wait_started_tick = tick
            if cic_tx_phase == 3 and not older_snapshot_alive:
                # Tx4 WaitForOlderSnapshots succeeds & sets indisvalid=true (indexcmds.c:1821-1832)
                cic_tx_phase = 4
                active_holders = [(m, rel) for (m, rel) in active_holders if m != SHARE_UPDATE_EXCLUSIVE]

            if cic_tx_phase in (1, 2, 3) and (tick - cic_wait_started_tick) >= per_wait_timeout_ticks:
                zombie_invalid_count += 1
                if cic_tx_phase >= 2:
                    zombie_indisready = True
                if strategy == "guarded_cic_preflight_cleanup":
                    # Mandatory post-abort DROP INDEX CONCURRENTLY removes invalid catalog residue
                    zombie_invalid_count -= 1
                    zombie_indisready = False
                cic_tx_phase = -1
                active_holders = [(m, rel) for (m, rel) in active_holders if m != SHARE_UPDATE_EXCLUSIVE]

        # Grant head of relation lock wait_queue if conflicts cleared
        while wait_queue:
            kind, wmode, _ = wait_queue[0]
            held_mask = 0
            for m, _ in active_holders:
                held_mask |= _bit(m)
            if (PG_CONFLICT_TAB[wmode] & held_mask) == 0:
                wait_queue.pop(0)
                dur = 50 if kind == "ddl" else 2
                active_holders.append((wmode, tick + dur))
            else:
                break

        held_mask = 0
        for m, _ in active_holders:
            held_mask |= _bit(m)
        wait_mask = 0
        for _, wm, _ in wait_queue:
            wait_mask |= _bit(wm)

        # Enforce hard 100-connection pool admission limit on OLTP arrivals (200 SELECT/s, 50 UPDATE/s)
        for _ in range(2):
            if (len(active_holders) + len(wait_queue)) >= pool_limit:
                rejected_selects += 1
            elif pg_lock_can_grant_immediately(ACCESS_SHARE, held_mask, wait_mask):
                active_holders.append((ACCESS_SHARE, tick + 2))
                held_mask |= _bit(ACCESS_SHARE)
            else:
                queued_selects += 1
                wait_queue.append(("select", ACCESS_SHARE, 999_999))
                wait_mask |= _bit(ACCESS_SHARE)

        if tick % 2 == 0:
            if (len(active_holders) + len(wait_queue)) >= pool_limit:
                rejected_updates += 1
            elif pg_lock_can_grant_immediately(ROW_EXCLUSIVE, held_mask, wait_mask):
                active_holders.append((ROW_EXCLUSIVE, tick + 2))
                held_mask |= _bit(ROW_EXCLUSIVE)
            else:
                queued_updates += 1
                wait_queue.append(("update", ROW_EXCLUSIVE, 999_999))
                wait_mask |= _bit(ROW_EXCLUSIVE)

        assert (len(active_holders) + len(wait_queue)) <= pool_limit
        if pool_exhausted_at_s is None and (len(active_holders) + len(wait_queue)) >= pool_limit:
            pool_exhausted_at_s = round((tick - ddl_tick) * dt, 3)

    return LockConvoyResult(
        strategy=strategy,
        pool_exhausted_at_s=pool_exhausted_at_s,
        queued_selects=queued_selects,
        rejected_selects=rejected_selects,
        queued_updates=queued_updates,
        rejected_updates=rejected_updates,
        zombie_invalid_count=zombie_invalid_count,
        zombie_indisready_write_amp=zombie_indisready,
        autovacuum_blocked=autovacuum_blocked,
    )


def run_probe_4() -> None:
    print("\n=== PROBE 4: PostgreSQL lock.c:1140 Wait-Mask Convoy & CONCURRENTLY Zombie Index ===")
    print("Provenance: [exact reproduction of pinned repository logic] + [controlled simulation]")

    for m1 in range(1, 9):
        for m2 in range(1, 9):
            assert bool(PG_CONFLICT_TAB[m1] & _bit(m2)) == bool(PG_CONFLICT_TAB[m2] & _bit(m1))
    assert bool(PG_CONFLICT_TAB[SHARE_UPDATE_EXCLUSIVE] & _bit(SHARE_UPDATE_EXCLUSIVE)) is True
    assert bool(PG_CONFLICT_TAB[SHARE] & _bit(ACCESS_SHARE)) is False

    res_alter = simulate_pg_ddl_strategy("alter_table_access_exclusive", long_holder_mode=ACCESS_SHARE)
    res_ci_writer = simulate_pg_ddl_strategy("create_index_share_lock", long_holder_mode=ROW_EXCLUSIVE)
    res_dexter_reader = simulate_pg_ddl_strategy("dexter_cic_5s_timeout", long_holder_mode=ACCESS_SHARE)
    res_dexter_3runs = simulate_pg_ddl_strategy(
        "dexter_cic_5s_timeout",
        long_holder_mode=ACCESS_SHARE,
        long_holder_duration_s=190.0,
        dexter_retry_runs=3,
    )
    res_guarded = simulate_pg_ddl_strategy("guarded_cic_preflight_cleanup", long_holder_mode=ACCESS_SHARE)

    assert res_alter.pool_exhausted_at_s == 0.38
    assert res_alter.queued_selects == 79 and res_alter.rejected_selects == 2_324
    assert res_alter.queued_updates == 20 and res_alter.rejected_updates == 581
    assert res_ci_writer.pool_exhausted_at_s == 1.86
    assert res_ci_writer.disrupted_selects == 0
    assert res_ci_writer.queued_updates == 95 and res_ci_writer.rejected_updates == 505
    assert res_dexter_reader.disrupted_selects == 0 and res_dexter_reader.disrupted_updates == 0
    assert res_dexter_reader.zombie_invalid_count == 1
    assert res_dexter_reader.zombie_indisready_write_amp is True
    assert res_dexter_reader.autovacuum_blocked is True
    assert res_dexter_3runs.zombie_invalid_count == 3  # indexer.rb:521 WHERE indisvalid = 't' blind spot
    assert res_guarded.disrupted_selects == 0 and res_guarded.disrupted_updates == 0
    assert res_guarded.zombie_invalid_count == 0

    print(
        f"  [4A] ALTER TABLE (AccessExclusive, lock_timeout=0 vs 12s SELECT, capped 100-conn pool): "
        f"pool exhausted in {res_alter.pool_exhausted_at_s:.2f}s "
        f"(disrupted_selects={res_alter.disrupted_selects} [queued={res_alter.queued_selects}, pool_rejected={res_alter.rejected_selects}], "
        f"disrupted_updates={res_alter.disrupted_updates} [queued={res_alter.queued_updates}, pool_rejected={res_alter.rejected_updates}])"
    )
    print(
        f"  [4B] CREATE INDEX (ShareLock, lock_timeout=0 vs 12s writer, capped 100-conn pool): "
        f"pool exhausted in {res_ci_writer.pool_exhausted_at_s:.2f}s "
        f"(disrupted_selects={res_ci_writer.disrupted_selects}, disrupted_updates={res_ci_writer.disrupted_updates} "
        f"[queued={res_ci_writer.queued_updates}, pool_rejected={res_ci_writer.rejected_updates}])"
    )
    print(
        f"  [4C] 4-tx CIC + per-wait lock_timeout='5s' vs read-only SELECT (Tx4 WaitForOlderSnapshots, indexcmds.c:1821): "
        f"convoy=0, zombie_indisvalid_false={res_dexter_reader.zombie_invalid_count} (3x_60s_Dexter_runs={res_dexter_3runs.zombie_invalid_count}), "
        f"indisready_write_amp={res_dexter_reader.zombie_indisready_write_amp}, autovacuum_blocked={res_dexter_reader.autovacuum_blocked}"
    )
    print(
        f"  [4D] Snapshot-preflight + auto-DROP guard: "
        f"disrupted_selects={res_guarded.disrupted_selects}, disrupted_updates={res_guarded.disrupted_updates}, "
        f"zombie_indisvalid_false={res_guarded.zombie_invalid_count}"
    )


# ==============================================================================
# PROBE 5: ORM N+1 vs IN-Batching, Multi-JOIN Blowup & Early Exit (Yang 2018)
# ==============================================================================


def run_probe_5() -> None:
    print("\n=== PROBE 5: Equal-Column ORM N+1 vs IN-Batching Crossover & Multi-JOIN Trap ===")
    print("Provenance: [real sqlite3 execution + analytical network-RTT crossover model]")

    conn = sqlite3.connect(":memory:")
    conn.executescript(
        """
        CREATE TABLE projects (id INTEGER PRIMARY KEY, name TEXT NOT NULL);
        CREATE TABLE issues (
            id INTEGER PRIMARY KEY,
            project_id INTEGER NOT NULL,
            state INTEGER NOT NULL,
            title TEXT NOT NULL
        );
        CREATE TABLE labels (
            id INTEGER PRIMARY KEY,
            project_id INTEGER NOT NULL,
            tag TEXT NOT NULL
        );
        """
    )

    n_projects = 120
    issues_per_proj = 60  # 7,200 issues
    labels_per_proj = 40  # 4,800 labels
    conn.executemany("INSERT INTO projects VALUES (?,?)", [(p, f"proj_{p}") for p in range(n_projects)])
    conn.executemany(
        "INSERT INTO issues VALUES (?,?,?,?)",
        [
            (p * issues_per_proj + j, p, j % 4, f"issue_{p}_{j}")
            for p in range(n_projects)
            for j in range(issues_per_proj)
        ],
    )
    conn.executemany(
        "INSERT INTO labels VALUES (?,?,?)",
        [
            (p * labels_per_proj + k, p, f"lbl_{k}")
            for p in range(n_projects)
            for k in range(labels_per_proj)
        ],
    )

    # 5A: Unindexed N+1 (ID + MI compound anti-pattern in Yang ICSE 2018, 2-col projection)
    proj_rows, vdbe_unidx_2col = count_vdbe_steps(conn, "SELECT id, name FROM projects")
    q_count_n1 = 1
    for pid, _ in proj_rows:
        _, st = count_vdbe_steps(conn, "SELECT id, title FROM issues WHERE project_id = ?", (pid,))
        vdbe_unidx_2col += st
        q_count_n1 += 1

    # Add foreign-key indexes and compare controlled equal-column projections + 1-child LEFT JOIN
    conn.execute("CREATE INDEX idx_issues_pid ON issues(project_id)")
    conn.execute("CREATE INDEX idx_labels_pid ON labels(project_id)")

    # Equal 2-column projection (SELECT id, title)
    proj_rows, vdbe_idx_n1_2col = count_vdbe_steps(conn, "SELECT id, name FROM projects")
    for pid, _ in proj_rows:
        _, st = count_vdbe_steps(conn, "SELECT id, title FROM issues WHERE project_id = ?", (pid,))
        vdbe_idx_n1_2col += st

    p_rows, vdbe_in_2col = count_vdbe_steps(conn, "SELECT id, name FROM projects")
    pids = tuple(r[0] for r in p_rows)
    placeholders = ",".join("?" for _ in pids)
    _, st_in_2col = count_vdbe_steps(
        conn, f"SELECT id, title FROM issues WHERE project_id IN ({placeholders})", pids
    )
    vdbe_in_2col += st_in_2col

    # Equal 3-column projection (SELECT project_id, id, title — required by ORM IN-preloaders to group by parent)
    proj_rows, vdbe_idx_n1_3col = count_vdbe_steps(conn, "SELECT id, name FROM projects")
    for pid, _ in proj_rows:
        _, st = count_vdbe_steps(conn, "SELECT project_id, id, title FROM issues WHERE project_id = ?", (pid,))
        vdbe_idx_n1_3col += st

    p_rows, vdbe_in_3col = count_vdbe_steps(conn, "SELECT id, name FROM projects")
    i_rows, st_in_3col = count_vdbe_steps(
        conn, f"SELECT project_id, id, title FROM issues WHERE project_id IN ({placeholders})", pids
    )
    vdbe_in_3col += st_in_3col
    q_count_in = 2

    # Single-child LEFT JOIN (projects p LEFT JOIN issues i — duplicates parent columns across 7,200 rows)
    join1_rows, vdbe_left_join_1child = count_vdbe_steps(
        conn,
        "SELECT p.id, p.name, i.id, i.title FROM projects p LEFT JOIN issues i ON i.project_id = p.id",
    )
    assert len(i_rows) == len(join1_rows) == n_projects * issues_per_proj

    # Latency model on equal 3-column projection: T_ms = queries * rtt_ms + vdbe_steps * 0.00001 ms
    op_ms = 0.00001
    lat_embedded_n1 = q_count_n1 * 0.0 + vdbe_idx_n1_3col * op_ms
    lat_embedded_in = q_count_in * 0.0 + vdbe_in_3col * op_ms
    lat_tcp_n1 = q_count_n1 * 0.50 + vdbe_idx_n1_3col * op_ms
    lat_tcp_in = q_count_in * 0.50 + vdbe_in_3col * op_ms

    # 5B: Multi-child LEFT JOIN Cartesian blowup (20 projects x 60 issues x 40 labels = 48,000 rows)
    sql_cartesian_join = """
        SELECT p.id, i.id, l.id
        FROM projects p
        LEFT JOIN issues i ON i.project_id = p.id
        LEFT JOIN labels l ON l.project_id = p.id
        WHERE p.id < 20
    """
    cart_rows, vdbe_cart = count_vdbe_steps(conn, sql_cartesian_join)

    p20, vdbe_split = count_vdbe_steps(conn, "SELECT id FROM projects WHERE id < 20")
    p20_ids = tuple(r[0] for r in p20)
    ph20 = ",".join("?" for _ in p20_ids)
    i20, st_i20 = count_vdbe_steps(conn, f"SELECT project_id, id FROM issues WHERE project_id IN ({ph20})", p20_ids)
    l20, st_l20 = count_vdbe_steps(conn, f"SELECT project_id, id FROM labels WHERE project_id IN ({ph20})", p20_ids)
    vdbe_split += st_i20 + st_l20
    split_total_tuples = len(p20) + len(i20) + len(l20)

    # 5C: Rails .any? (SELECT COUNT(*)) vs .exists? (SELECT 1 ... LIMIT 1) on unindexed predicate
    cnt_res, vdbe_count_star = count_vdbe_steps(conn, "SELECT COUNT(*) FROM issues WHERE state = 0")
    ex_res, vdbe_exists_lim1 = count_vdbe_steps(conn, "SELECT 1 FROM issues WHERE state = 0 LIMIT 1")
    conn.close()

    assert cnt_res[0][0] > 0 and ex_res == [(1,)]
    assert vdbe_unidx_2col == 2_614_927
    # Equal-column IN-batching executes strictly FEWER VDBE instructions than N+1 (by 228 ops at both widths),
    # whereas 2-col N+1 (44,886) vs 3-col IN (51,858) differs only by 7,200 OP_Column extractions of project_id!
    assert vdbe_in_2col == 44_658 and vdbe_idx_n1_2col == 44_886 and vdbe_in_2col < vdbe_idx_n1_2col
    assert vdbe_in_3col == 51_858 and vdbe_idx_n1_3col == 52_086 and vdbe_in_3col < vdbe_idx_n1_3col
    assert vdbe_left_join_1child == 65_408 and vdbe_left_join_1child > vdbe_in_3col
    assert 1.0 < (vdbe_idx_n1_2col / vdbe_in_2col) < 1.01
    assert lat_tcp_n1 / lat_tcp_in > 35.0
    assert len(cart_rows) == 48_000 and split_total_tuples == 2_020
    assert vdbe_cart / vdbe_split > 30.0
    assert vdbe_count_star / vdbe_exists_lim1 > 1_000.0

    print(
        f"  [5A] Controlled SQLite B-tree N+1 vs IN (120 parents, 7200 children): "
        f"unindexed_2col_N+1={vdbe_unidx_2col} ops | equal_2col: IN={vdbe_in_2col} < N+1={vdbe_idx_n1_2col} "
        f"({vdbe_idx_n1_2col / vdbe_in_2col:.4f}x) | equal_3col: IN={vdbe_in_3col} < N+1={vdbe_idx_n1_3col} "
        f"({lat_embedded_n1:.3f}ms vs {lat_embedded_in:.3f}ms @ 0ms RTT; "
        f"{lat_tcp_n1:.2f}ms vs {lat_tcp_in:.2f}ms @ 0.5ms TCP = {lat_tcp_n1 / lat_tcp_in:.1f}x penalty) | "
        f"1child_LEFT_JOIN={vdbe_left_join_1child} ops"
    )
    print(
        f"  [5B] 2-collection LEFT JOIN Cartesian blowup (20 projects): "
        f"JOIN_rows={len(cart_rows)} ({vdbe_cart} ops) vs 3_query_IN_rows={split_total_tuples} ({vdbe_split} ops, "
        f"{len(cart_rows) / split_total_tuples:.1f}x row blowup, {vdbe_cart / vdbe_split:.1f}x VDBE blowup)"
    )
    print(
        f"  [5C] Existence check early termination (state=0): "
        f"COUNT(*)={vdbe_count_star} ops vs SELECT_1_LIMIT_1={vdbe_exists_lim1} ops "
        f"({vdbe_count_star / vdbe_exists_lim1:.1f}x reduction)"
    )


def main() -> None:
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    run_probe_5()
    print("\nALL 5 DATABASE TUNING, OPTIMIZER PLAN, AND LOCK-CONVOY PROBES VERIFIED SUCCESSFULLY.")


if __name__ == "__main__":
    main()
