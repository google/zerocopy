#!/usr/bin/env python3
"""Deterministic verification probes for quantitative data analysis, enterprise SQL
generation, machine-learning engineering search, and scientific discovery workflows.

Self-contained support script for the reference report package:
  reports/agent-data-analysis-sql-generation-ml-experimentation-and-scientific-workflows/

Design invariants:
- Python 3.10+ standard library only (zero third-party dependencies, zero network,
  zero disk writes).
- Fixed seed (SEED = 20261121), no timestamps or wall-clock output in stdout.
- Bit-identical stdout and SHA-256 across repeated runs (`python3 -I -B`).
- Explicit epistemic banners separating exact source/SQL reproductions, analytical
  derivations, and controlled tabular / statistical experiments:
  * Probe 1a (`[exact reproduction of pinned SQL/evaluator logic]`):
      SQLite3 execution of `emorynlp/ETM@21f6ea7de6` `treeMatch.py:1738-1803` (`rule25`)
      unconditional `LEFT JOIN ... IS NULL -> NOT IN` rewrite under SQL 3-valued NULLs
      and nullable non-key predicates vs. `NOT EXISTS`.
  * Probe 1b (`[toy model / controlled tabular experiment]`):
      Controlled SQLite3 relational verification of `1:N x 1:M` chasm-trap join fan-out
      (`6.0x` sum inflation) vs. pre-aggregated `1:1` CTE grain guard.
  * Probe 1c (`[exact reproduction of pinned SQL/evaluator logic]`):
      Exact reproduction of `xlang-ai/Spider2@cafb867313` `spider2-lite/evaluation_suite/evaluate.py:84-131`
      (`NULL -> 0` coercion, transposed independent column sorting under `ignore_order=True`,
      non-injective `any(...)` column check, and `abs_tol=1e-2`) vs. `sound_compare_table`
      using numeric `float(x)` row sorting + exact bipartite row matching under `(rel_tol, abs_tol)`,
      including the `0.999999` vs. `1.000001` mantissa/exponent boundary positive control.
  * Probe 1d (`[exact analytical / derived calculation] + [toy model / controlled tabular experiment]`):
      `CHASE-SQL` Algorithm 3 (`arXiv:2410.01943v1` Sec. 3.5, L314-341; Table 5) comparison
      separating literal ordered pairs (`i != j`, 238 calls: E[r_c] = K - 2p independent of m,
      `89.02%` win rate, yet violating Tideman/Copeland Clone Independence under cyclic preferences)
      from unordered-pair misimplementations (`i < j`, 119 calls: m > 2Kp - K + 1 intra-cluster
      subsidy, `15.25%` win rate) and budget-matched pre-tournament execution-cluster deduplication
      with iterative Bradley-Terry MLE (`94.35%` win rate at 196 calls and strict clone independence).
  * Probe 2 (`[exact reproduction of pinned SQL/evaluator logic]`):
      Exact reproduction of `ShayanTalaei/CHESS@3d6e835f85` `preprocess.py:40,87-90`,
      `search.py:48-78`, and `retrieve_entity.py:252-275` (`difflib.SequenceMatcher`),
      reporting both uniform 62-short-code recall (`10/62 = 16.13%` under `top_n=10`) and
      substring-dropped business-column recall (`0.0%`) vs. token-boundary + padded `(1,2,3)`-gram fix.
  * Probe 3a (`[exact reproduction of pinned SQL/evaluator logic]`):
      Exact reproduction of `WecoAI/aideml@ad73d227af` `aide/journal.py:162-228`
      `_metric_rank` direction-conflict selection bug.
  * Probe 3b (`[toy model / controlled tabular experiment]`):
      De-confounded grouped-tabular closed-form Ridge regression search (`N=240` across 120 entities,
      matched 192-row refits) isolating pure greedy `GroupKFold` (`clean=0.3841`, `5.0%` benign
      Frisch-Waugh-Lovell entity-demeaning selection) from `-0.004 * len(act)` parsimony penalty
      and top-3 beam (`0.0%` hijack, `test_r2=0.3877`), cross-referencing corpus package
      `reusable-holdout-thresholdout-ladder-leaderboards-and-clopper-pearson-zero-numerators`.
  * Probe 4a (`[exact reproduction of pinned SQL/evaluator logic] + [exact analytical / derived calculation]`):
      Exact reproduction of `allenai/discoverybench@c31fcf011e` `eval/new_eval.py:386-435`
      (`recall * precision * bar_s` vs. paper `ctx_F1 * bar_s`, plus unsegmented-hypothesis leakage).
  * Probe 4b (`[toy model / controlled tabular experiment]`):
      Controlled `M=48` multiverse ablation (`rho = 0.60` and `rho = 0.85`) demonstrating why
      Confirmatory Lockbox evaluation must verify the specification curve (sign agreement +
      directional median z) rather than only the single lowest-p discovery specification.
  * Probe 5a (`[toy model / controlled tabular experiment]`):
      Controlled SQLite3 model of `DABstep` (`arXiv:2506.23719v1` App. A.4) static-column fee-rule
      fan-out (`+95.45%` bps inflation) with dynamic `PRAGMA table_info` unconsumed-column detection.
  * Probe 5b (`[exact reproduction of pinned SQL/evaluator logic]`):
      Exact reproduction of `Future-House/BixBench@49311180bd` `bixbench/graders.py:65-108,155-170`
      and root `grade_outputs.py:70-80` (including live baseline false positive `bix-53-q4`:
      `"5"` vs. `"4.25E-04"` graded `1`), paired with a numeric/token-boundary hardened verifier
      tested against sign, scientific-exponent, substring-token, and numeric-prefix adversarial inputs.
"""

from __future__ import annotations

import ast
from difflib import SequenceMatcher
import hashlib
import json
import math
import random
import re
import sqlite3
import statistics
import struct


SEED = 20261121

B_EXACT_CODE = "[exact reproduction of pinned SQL/evaluator logic]"
B_ANALYTICAL = "[exact analytical / derived calculation]"
B_CONTROLLED = "[toy model / controlled tabular experiment]"


# ===========================================================================
# Probe 1: SQL Silent Corruption, Spider2 Evaluator, ETM Rule 25 & CHASE-SQL
# ===========================================================================
def run_probe_p1() -> dict:
    conn = sqlite3.connect(":memory:")
    cur = conn.cursor()
    cur.executescript(
        """
        CREATE TABLE customers (cid INTEGER PRIMARY KEY, name TEXT NOT NULL);
        CREATE TABLE orders (oid INTEGER PRIMARY KEY, cid INTEGER NULL, coupon TEXT NULL);
        INSERT INTO customers VALUES (1, 'Alice'), (2, 'Bob'), (3, 'Carol'), (4, 'Dave'), (5, 'Eve');
        -- Customer 1 placed order with coupon; Customer 2 placed order with NULL coupon;
        -- Order 103 is a guest checkout (cid IS NULL); Customers 3, 4, 5 placed no orders.
        INSERT INTO orders VALUES (101, 1, 'SAVE10'), (102, 2, NULL), (103, NULL, 'GUEST5');

        CREATE TABLE invoices (inv_id INTEGER PRIMARY KEY, cust_id INTEGER, amount REAL);
        CREATE TABLE shipments (ship_id INTEGER PRIMARY KEY, inv_id INTEGER, carrier TEXT);
        CREATE TABLE line_notes (note_id INTEGER PRIMARY KEY, inv_id INTEGER, note TEXT);
        INSERT INTO invoices VALUES (1, 10, 100.0), (2, 10, 250.0);
        INSERT INTO shipments VALUES
            (1, 1, 'UPS'), (2, 1, 'UPS'), (3, 1, 'DHL'),
            (4, 2, 'UPS'), (5, 2, 'FedEx'), (6, 2, 'DHL');
        INSERT INTO line_notes VALUES
            (1, 1, 'fragile'), (2, 1, 'insured'),
            (3, 2, 'priority'), (4, 2, 'customs');

        CREATE TABLE equities (ticker TEXT PRIMARY KEY, sector TEXT NOT NULL);
        CREATE TABLE returns_q4 (ticker TEXT PRIMARY KEY, q4_ret REAL);
        INSERT INTO equities VALUES ('AAPL', 'Tech'), ('GOOG', 'Tech'), ('MSFT', 'Tech');
        -- MSFT has no returns_q4 row -> LEFT JOIN yields NULL for MSFT's q4_ret
        INSERT INTO returns_q4 VALUES ('AAPL', 0.25), ('GOOG', -0.15);
        """
    )

    # Probe 1a. [exact reproduction of pinned SQL/evaluator logic]
    # emorynlp/ETM@21f6ea7de6 treeMatch.py:1738-1803 (rule25) rewrites ANY single-LEFT-JOIN
    # query of the form:
    #   SELECT ... FROM a LEFT JOIN b ON a.c1 = b.c2 WHERE b.<any_col> IS NULL
    # unconditionally to:
    #   SELECT ... FROM a WHERE a.c1 NOT IN (SELECT b.c2 FROM b)
    # without inspecting `schema` (unused arg!) for NOT NULL on b.c2 or checking b.<any_col> == b.c2.
    q_left_fk = [
        r[0]
        for r in cur.execute(
            "SELECT customers.cid FROM customers LEFT JOIN orders "
            "ON customers.cid = orders.cid WHERE orders.cid IS NULL ORDER BY customers.cid"
        )
    ]
    q_left_nullable_nonkey = [
        r[0]
        for r in cur.execute(
            "SELECT customers.cid FROM customers LEFT JOIN orders "
            "ON customers.cid = orders.cid WHERE orders.coupon IS NULL ORDER BY customers.cid"
        )
    ]
    q_etm_rule25_rewrite = [
        r[0]
        for r in cur.execute(
            "SELECT customers.cid FROM customers "
            "WHERE customers.cid NOT IN (SELECT orders.cid FROM orders) ORDER BY customers.cid"
        )
    ]
    q_safe_not_exists = [
        r[0]
        for r in cur.execute(
            "SELECT customers.cid FROM customers "
            "WHERE NOT EXISTS (SELECT 1 FROM orders WHERE orders.cid = customers.cid) "
            "ORDER BY customers.cid"
        )
    ]
    assert q_left_fk == [3, 4, 5]
    assert q_left_nullable_nonkey == [2, 3, 4, 5]
    assert q_etm_rule25_rewrite == []  # SQL 3VL: x NOT IN (1, 2, NULL) -> UNKNOWN -> 0 rows
    assert q_safe_not_exists == [3, 4, 5]

    # Probe 1b. [toy model / controlled tabular experiment]
    # Controlled SQLite3 verification of 1:N x 1:M chasm-trap fan-out vs. CTE grain-guarded pre-aggregation.
    true_invoice_sum = cur.execute("SELECT SUM(amount) FROM invoices").fetchone()[0]
    naive_sum, join_rows, distinct_pks = cur.execute(
        """
        SELECT SUM(i.amount), COUNT(*), COUNT(DISTINCT i.inv_id)
        FROM invoices i
        JOIN shipments s ON i.inv_id = s.inv_id
        JOIN line_notes n ON i.inv_id = n.inv_id
        """
    ).fetchone()
    guarded_cte_sum = cur.execute(
        """
        WITH ship_agg AS (SELECT inv_id, COUNT(*) AS n_ships FROM shipments GROUP BY inv_id),
             note_agg AS (SELECT inv_id, COUNT(*) AS n_notes FROM line_notes GROUP BY inv_id)
        SELECT SUM(i.amount)
        FROM invoices i
        LEFT JOIN ship_agg s ON i.inv_id = s.inv_id
        LEFT JOIN note_agg n ON i.inv_id = n.inv_id
        """
    ).fetchone()[0]
    fanout_ratio = join_rows / distinct_pks
    assert math.isclose(true_invoice_sum, 350.0)
    assert math.isclose(naive_sum, 2100.0) and math.isclose(fanout_ratio, 6.0)
    assert math.isclose(guarded_cte_sum, 350.0)

    # Probe 1c. [exact reproduction of pinned SQL/evaluator logic]
    # Exact line-for-line port of xlang-ai/Spider2@cafb867313aab4e674652054198f383cf4018943
    # spider2-lite/evaluation_suite/evaluate.py:84-131:
    # - spider2-lite/evaluation_suite/gold/spider2lite_eval.jsonl sets "ignore_order": true on 547/547 (100.0%),
    #   with 463/547 (84.64%) multi-column tasks and 84/547 single-column tasks;
    # - spider2-snow/evaluation_suite/gold/spider2snow_eval.jsonl sets "ignore_order": true on 547/547 (100.0%);
    # - spider2-dbt/evaluation_suite/gold/spider2_eval.jsonl sets nested evaluation.parameters.ignore_orders
    #   to all-True on 68/68 (100.0%) tasks in duckdb_match (eval_utils.py:184-244).
    def is_na(v: object) -> bool:
        return v is None or (isinstance(v, float) and math.isnan(v))

    def is_num(v: object) -> bool:
        return isinstance(v, (int, float)) and not isinstance(v, bool) and not is_na(v)

    def spider2_compare_pandas_table(
        pred_rows: list[tuple],
        gold_rows: list[tuple],
        condition_cols: list[int] | None = None,
        ignore_order: bool = False,
    ) -> int:
        tolerance = 1e-2

        def normalize(value):
            if is_na(value):
                return 0
            return value

        def vectors_match(v1, v2, tol=tolerance, ignore_order_=False):
            v1 = [normalize(x) for x in v1]
            v2 = [normalize(x) for x in v2]
            if ignore_order_:
                v1 = sorted(
                    v1, key=lambda x: (x is None, str(x), isinstance(x, (int, float)))
                )
                v2 = sorted(
                    v2, key=lambda x: (x is None, str(x), isinstance(x, (int, float)))
                )
            if len(v1) != len(v2):
                return False
            for a, b in zip(v1, v2):
                if is_na(a) and is_na(b):
                    continue  # Dead code in evaluate.py:104-105 due to normalize()
                if isinstance(a, (int, float)) and isinstance(b, (int, float)):
                    if not math.isclose(float(a), float(b), abs_tol=tol):
                        return False
                elif a != b:
                    return False
            return True

        gold_T = list(zip(*gold_rows)) if gold_rows else []
        if condition_cols:
            gold_T = [gold_T[idx] for idx in condition_cols]
        pred_T = list(zip(*pred_rows)) if pred_rows else []
        score = 1
        for gold_vector in gold_T:
            if not any(
                vectors_match(list(gold_vector), list(pred_vector), ignore_order_=ignore_order)
                for pred_vector in pred_T
            ):
                score = 0
                break
        return score

    def rows_close(pr: tuple, gr: tuple, rel_tol: float, abs_tol: float) -> bool:
        if len(pr) != len(gr):
            return False
        for a, b in zip(pr, gr):
            if is_na(a) != is_na(b):
                return False
            if is_na(a):
                continue
            if is_num(a) and is_num(b):
                if not math.isclose(float(a), float(b), rel_tol=rel_tol, abs_tol=abs_tol):
                    return False
            elif is_num(a) != is_num(b) or a != b:
                return False
        return True

    def sound_compare_table(
        pred_rows: list[tuple],
        gold_rows: list[tuple],
        rel_tol: float = 1e-4,
        abs_tol: float = 1e-6,
        ignore_order: bool = True,
    ) -> int:
        if len(pred_rows) != len(gold_rows):
            return 0
        if not gold_rows:
            return 1
        n_cols = len(gold_rows[0])
        if any(len(r) != n_cols for r in pred_rows) or any(len(r) != n_cols for r in gold_rows):
            return 0
        if not ignore_order:
            return int(all(rows_close(pr, gr, rel_tol, abs_tol) for pr, gr in zip(pred_rows, gold_rows)))

        # Sort numeric cells by numeric float(x) (never lexicographic scientific-notation strings,
        # where "+9.999990e-01" > "+5.000000e+00"!). Tuple slot 1 isolates float(x) from str(x).
        def row_sort_key(row: tuple) -> tuple:
            out = []
            for x in row:
                if is_na(x):
                    out.append((1, 0, 0.0))
                elif is_num(x):
                    out.append((0, 0, float(x)))
                else:
                    out.append((0, 1, str(x)))
            return tuple(out)

        p_seq = sorted(pred_rows, key=row_sort_key)
        g_seq = sorted(gold_rows, key=row_sort_key)
        if all(rows_close(pr, gr, rel_tol, abs_tol) for pr, gr in zip(p_seq, g_seq)):
            return 1

        # Exact augmenting-path bipartite matching fallback when near-equal floats invert sort order
        # within (rel_tol, abs_tol) across rows sharing categorical keys.
        n_r = len(g_seq)
        adj = [
            [j for j in range(n_r) if rows_close(p_seq[i], g_seq[j], rel_tol, abs_tol)]
            for i in range(n_r)
        ]
        match_gold = [-1] * n_r

        def try_kuhn(u: int, seen: list[bool]) -> bool:
            for v in adj[u]:
                if seen[v]:
                    continue
                seen[v] = True
                if match_gold[v] == -1 or try_kuhn(match_gold[v], seen):
                    match_gold[v] = u
                    return True
            return False

        for i in range(n_r):
            if not try_kuhn(i, [False] * n_r):
                return 0
        return 1

    gold_eq_rows = cur.execute(
        "SELECT e.ticker, r.q4_ret FROM equities e "
        "LEFT JOIN returns_q4 r ON e.ticker = r.ticker ORDER BY e.ticker ASC"
    ).fetchall()
    reordered_valid_rows = cur.execute(
        "SELECT e.ticker, r.q4_ret FROM equities e "
        "LEFT JOIN returns_q4 r ON e.ticker = r.ticker ORDER BY e.ticker DESC"
    ).fetchall()
    corrupted_eq_rows = cur.execute(
        """
        WITH ranked_e AS (SELECT ticker, ROW_NUMBER() OVER (ORDER BY ticker ASC) AS rn FROM equities),
             shifted_r AS (
                 SELECT -0.15 AS bad_ret, 1 AS rn UNION ALL
                 SELECT 0.004 AS bad_ret, 2 AS rn UNION ALL
                 SELECT 0.25  AS bad_ret, 3 AS rn
             )
        SELECT ranked_e.ticker, shifted_r.bad_ret, 'EXTRA_GARBAGE_COL'
        FROM ranked_e JOIN shifted_r ON ranked_e.rn = shifted_r.rn
        """
    ).fetchall()

    spider2_corrupted_score = spider2_compare_pandas_table(
        corrupted_eq_rows, gold_eq_rows, ignore_order=True
    )
    sound_corrupted_score = sound_compare_table(
        corrupted_eq_rows, gold_eq_rows, ignore_order=True
    )
    sound_reordered_valid_score = sound_compare_table(
        reordered_valid_rows, gold_eq_rows, ignore_order=True
    )
    # Positive control 1: exponent boundary 0.999999 vs 1.000001 alongside 5.0 (rel_err = 2e-6 < 1e-4)
    sound_exp_boundary_pos_ctrl = sound_compare_table(
        [("Tech", 1.000001), ("Tech", 5.0)],
        [("Tech", 0.999999), ("Tech", 5.0)],
        ignore_order=True,
    )
    # Positive control 2: near-tie float inversion across distinct row labels within rel_tol
    sound_near_tie_bipartite_pos_ctrl = sound_compare_table(
        [("Tech", 1.000000, "A"), ("Tech", 1.000002, "B")],
        [("Tech", 1.000003, "A"), ("Tech", 0.999999, "B")],
        ignore_order=True,
    )
    # Negative control: genuinely swapped row bindings outside tolerance must score 0
    sound_swapped_binding_neg_ctrl = sound_compare_table(
        [("Tech", 1.0, "A"), ("Tech", 5.0, "B")],
        [("Tech", 1.0, "B"), ("Tech", 5.0, "A")],
        ignore_order=True,
    )
    assert spider2_corrupted_score == 1
    assert sound_corrupted_score == 0
    assert sound_reordered_valid_score == 1
    assert sound_exp_boundary_pos_ctrl == 1
    assert sound_near_tie_bipartite_pos_ctrl == 1
    assert sound_swapped_binding_neg_ctrl == 0

    # Probe 1d. [exact analytical / derived calculation] + [toy model / controlled tabular experiment]
    # CHASE-SQL Algorithm 3 (arXiv:2410.01943v1 Sec. 3.5, L314-341; Table 5 binary accuracies).
    K = 21
    m_wrong = 14
    p_flash = 0.7101  # Table 5: Tuned Gemini-1.5-flash binary accuracy
    p_sonnet = 0.6021  # Table 5: Untuned Claude-3.5-sonnet binary accuracy

    # (i-a) Literal ordered pairs (1 <= i != j <= K, L318 + L333, 238 LLM calls at m=14):
    # Every wrong candidate gets (m-1) intra-cluster pts + (K-m-1) wrong-vs-wrong pts + 2*(1-p) vs c*
    # => E[r_c] = K - 2p (independent of m!), whereas E[r_c*] = 2*(K-1)*p.
    exp_wrong_ordered = K - 2.0 * p_flash
    exp_cstar_ordered = 2.0 * (K - 1) * p_flash
    assert math.isclose(round(exp_wrong_ordered, 4), 19.5798)
    assert math.isclose(round(exp_cstar_ordered, 4), 28.4040)

    # (i-b) Unordered-pair misimplementation (1 <= i < j <= K, 119 LLM calls at m=14):
    # Asymmetric `w <- i` concentrates m-1 intra-cluster points onto c_0, beating c* iff m > 2Kp - K + 1.
    exp_c0_unordered_asym = 0.5 * (K + m_wrong - 1) - p_flash
    exp_c_unordered_sym_nc = 0.5 * K - p_flash
    exp_cstar_unordered = (K - 1) * p_flash
    crit_m_unordered_flash = 2 * K * p_flash - K + 1
    crit_m_unordered_sonnet = 2 * K * p_sonnet - K + 1
    assert exp_c0_unordered_asym > exp_cstar_unordered > exp_c_unordered_sym_nc

    # (ii) Exact algebraic demonstration of Copeland Clone-Multiplicity Distortion under
    # literal ORDERED pairs (i != j), cured unconditionally by pre-tournament cluster deduplication.
    directed_wins = {
        ("C*", "A1"): 2, ("A1", "C*"): 0,
        ("C*", "A2"): 2, ("A2", "C*"): 0,
        ("C*", "B"): 1,  ("B", "C*"): 1,
        ("C*", "D"): 0,  ("D", "C*"): 2,
        ("A1", "A2"): 1, ("A2", "A1"): 1,
        ("A1", "B"): 1,  ("B", "A1"): 1,
        ("A1", "D"): 2,  ("D", "A1"): 0,
        ("A2", "B"): 1,  ("B", "A2"): 1,
        ("A2", "D"): 2,  ("D", "A2"): 0,
        ("D", "B"): 2,   ("B", "D"): 0,
    }

    def ordered_alg3_scores(pool_clusters: list[str]) -> dict[str, int]:
        n_c = len(pool_clusters)
        sc = [0] * n_c
        for i in range(n_c):
            for j in range(n_c):
                if i == j:
                    continue
                ci, cj = pool_clusters[i], pool_clusters[j]
                if ci == cj:
                    sc[i] += 1
                elif i < j:
                    w_ij = directed_wins[(ci, cj)]
                    sc[i] += w_ij
                    sc[j] += 2 - w_ij
        out: dict[str, int] = {}
        for idx, cl in enumerate(pool_clusters):
            out[cl] = max(out.get(cl, 0), sc[idx])
        return out

    def bradley_terry_mm_winners(
        wins_mat: list[list[float]], n_mat: list[list[float]], iters: int = 40
    ) -> list[int]:
        u_cnt = len(wins_mat)
        pi = [1.0] * u_cnt
        for _ in range(iters):
            nxt = [1.0] * u_cnt
            for i in range(u_cnt):
                w_i = sum(wins_mat[i]) + 1e-6
                denom = (
                    sum(
                        n_mat[i][j] / (pi[i] + pi[j])
                        for j in range(u_cnt)
                        if j != i and n_mat[i][j] > 0
                    )
                    + 2e-6
                )
                nxt[i] = w_i / denom
            s = sum(nxt)
            pi = [x * u_cnt / s for x in nxt]
        mx = max(pi)
        return [i for i, x in enumerate(pi) if abs(x - mx) <= 1e-9]

    def dedup_bt_winner(pool_clusters: list[str]) -> str:
        uniq = list(dict.fromkeys(pool_clusters))
        u_n = len(uniq)
        w_m = [[0.0] * u_n for _ in range(u_n)]
        n_m = [[0.0] * u_n for _ in range(u_n)]
        for a in range(u_n):
            for b in range(a + 1, u_n):
                w_ab = directed_wins[(uniq[a], uniq[b])]
                w_m[a][b] = float(w_ab)
                w_m[b][a] = float(2 - w_ab)
                n_m[a][b] = 2.0
                n_m[b][a] = 2.0
        winners = bradley_terry_mm_winners(w_m, n_m)
        return uniq[winners[0]]

    dedup_ordered_sc = ordered_alg3_scores(["C*", "A1", "A2", "D", "B"])
    cloned_ordered_sc = ordered_alg3_scores(["C*", "A1", "A2", "D"] + ["B"] * 4)
    dedup_ordered_winner = max(dedup_ordered_sc, key=lambda k: dedup_ordered_sc[k])
    cloned_ordered_winner = max(cloned_ordered_sc, key=lambda k: cloned_ordered_sc[k])
    cloned_dedup_bt_winner = dedup_bt_winner(["C*", "A1", "A2", "D"] + ["B"] * 4)
    assert dedup_ordered_sc == {"C*": 5, "D": 4, "A1": 4, "A2": 4, "B": 3}
    assert dedup_ordered_winner == "C*"
    assert cloned_ordered_sc["D"] == 10 and cloned_ordered_sc["C*"] == 8
    assert cloned_ordered_winner == "D"
    assert cloned_dedup_bt_winner == "C*"  # Strictly clone-independent!

    # (iii) Seeded stochastic tournament comparison (n=2,000 tournaments, U=8 unique clusters)
    clusters = [0] * m_wrong + [1, 2, 3, 4, 5, 6] + [7]  # 7 is unique correct SQL c*
    n_tournaments = 2000

    # Unordered (119 calls) vs symmetric tie-split NC vs naive unweighted 1-vote/3-vote dedup
    rng = random.Random(SEED)
    wins_asym_first_tie = 0.0
    wins_asym_fair_tie = 0.0
    wins_sym_nc = 0.0
    wins_dedup_1vote = 0.0
    wins_dedup_3vote = 0.0

    for _ in range(n_tournaments):
        sc_asym = [0.0] * K
        sc_sym = [0.0] * K
        for i in range(K):
            for j in range(i + 1, K):
                if clusters[i] == clusters[j]:
                    sc_asym[i] += 1.0
                    sc_sym[i] += 0.5
                    sc_sym[j] += 0.5
                else:
                    p_j_wins = (
                        p_flash if clusters[j] == 7 else ((1.0 - p_flash) if clusters[i] == 7 else 0.5)
                    )
                    if rng.random() < p_j_wins:
                        sc_asym[j] += 1.0
                        sc_sym[j] += 1.0
                    else:
                        sc_asym[i] += 1.0
                        sc_sym[i] += 1.0

        if max(range(K), key=lambda idx: sc_asym[idx]) == 20:
            wins_asym_first_tie += 1.0
        max_a = max(sc_asym)
        tied_a = [idx for idx, v in enumerate(sc_asym) if math.isclose(v, max_a)]
        if 20 in tied_a:
            wins_asym_fair_tie += 1.0 / len(tied_a)

        max_s = max(sc_sym)
        tied_s = [idx for idx, v in enumerate(sc_sym) if math.isclose(v, max_s)]
        if 20 in tied_s:
            wins_sym_nc += 1.0 / len(tied_s)

        u_sc_1 = [0] * 8
        u_sc_3 = [0] * 8
        for ua in range(8):
            for ub in range(ua + 1, 8):
                p_b = p_flash if ub == 7 else ((1.0 - p_flash) if ua == 7 else 0.5)
                v1 = int(rng.random() < p_b)
                v2 = int(rng.random() < p_b)
                v3 = int(rng.random() < p_b)
                if v1 == 1:
                    u_sc_1[ub] += 1
                else:
                    u_sc_1[ua] += 1
                if (v1 + v2 + v3) >= 2:
                    u_sc_3[ub] += 1
                else:
                    u_sc_3[ua] += 1

        m1 = max(u_sc_1)
        t1 = [u for u, v in enumerate(u_sc_1) if v == m1]
        if 7 in t1:
            wins_dedup_1vote += 1.0 / len(t1)

        m3 = max(u_sc_3)
        t3 = [u for u, v in enumerate(u_sc_3) if v == m3]
        if 7 in t3:
            wins_dedup_3vote += 1.0 / len(t3)

    # Literal ordered-pair Alg. 3 (i != j, 238 directed LLM calls) on identical seed
    rng_ord = random.Random(SEED)
    wins_ord_first_tie = 0.0
    wins_ord_fair_tie = 0.0
    for _ in range(n_tournaments):
        sc_ord = [0.0] * K
        for i in range(K):
            for j in range(K):
                if i == j:
                    continue
                if clusters[i] == clusters[j]:
                    sc_ord[i] += 1.0
                else:
                    p_j_wins = (
                        p_flash if clusters[j] == 7 else ((1.0 - p_flash) if clusters[i] == 7 else 0.5)
                    )
                    if rng_ord.random() < p_j_wins:
                        sc_ord[j] += 1.0
                    else:
                        sc_ord[i] += 1.0
        if max(range(K), key=lambda idx: sc_ord[idx]) == 20:
            wins_ord_first_tie += 1.0
        max_o = max(sc_ord)
        tied_o = [idx for idx, v in enumerate(sc_ord) if math.isclose(v, max_o)]
        if 20 in tied_o:
            wins_ord_fair_tie += 1.0 / len(tied_o)

    # Budget-matched pre-deduplicated cluster tournament (7 votes/pair = 196 calls < 238 calls):
    # evaluates both per-pair majority Copeland and Bradley-Terry MLE (by Zermelo 1929 / Ford 1957,
    # under equal pair sample size n_{ab} = v = 7, strict concavity of the BT log-likelihood implies
    # pi_hat_u > pi_hat_u' iff total win count W_u > W_u'; verified directly against 40-iter MM on
    # the first 100 tournaments).
    rng_bt = random.Random(SEED)
    wins_dedup_7vote_maj = 0.0
    wins_dedup_7vote_bt = 0.0
    for t_idx in range(n_tournaments):
        u_maj7 = [0] * 8
        u_wsum = [0] * 8
        w_mat = [[0.0] * 8 for _ in range(8)] if t_idx < 100 else None
        n_mat = [[7.0 if a != b else 0.0 for b in range(8)] for a in range(8)] if t_idx < 100 else None
        for ua in range(8):
            for ub in range(ua + 1, 8):
                p_b = p_flash if ub == 7 else ((1.0 - p_flash) if ua == 7 else 0.5)
                vb = sum(int(rng_bt.random() < p_b) for _ in range(7))
                va = 7 - vb
                if vb >= 4:
                    u_maj7[ub] += 1
                else:
                    u_maj7[ua] += 1
                u_wsum[ub] += vb
                u_wsum[ua] += va
                if w_mat is not None:
                    w_mat[ub][ua] = float(vb)
                    w_mat[ua][ub] = float(va)
        m7 = max(u_maj7)
        t7 = [u for u, v in enumerate(u_maj7) if v == m7]
        if 7 in t7:
            wins_dedup_7vote_maj += 1.0 / len(t7)
        mw = max(u_wsum)
        t_bt = [u for u, v in enumerate(u_wsum) if v == mw]
        if w_mat is not None and n_mat is not None:
            assert bradley_terry_mm_winners(w_mat, n_mat) == t_bt
        if 7 in t_bt:
            wins_dedup_7vote_bt += 1.0 / len(t_bt)

    r_asym_first = wins_asym_first_tie / n_tournaments
    r_asym = wins_asym_fair_tie / n_tournaments
    r_sym = wins_sym_nc / n_tournaments
    r_dedup1 = wins_dedup_1vote / n_tournaments
    r_dedup3 = wins_dedup_3vote / n_tournaments
    r_ord_first = wins_ord_first_tie / n_tournaments
    r_ord_fair = wins_ord_fair_tie / n_tournaments
    r_dedup7_maj = wins_dedup_7vote_maj / n_tournaments
    r_dedup7_bt = wins_dedup_7vote_bt / n_tournaments

    assert r_asym_first < 0.12 and r_asym < 0.18
    assert r_sym > 0.65
    assert math.isclose(round(r_ord_fair, 4), 0.8902) and math.isclose(round(r_ord_first, 4), 0.8690)
    assert r_ord_fair > r_dedup3 > r_dedup1
    assert r_dedup7_bt > r_ord_fair  # 94.45% at 196 calls > 89.02% at 238 calls + clone-independent!

    conn.close()
    return {
        "etm_rule25_sqlite": {
            "left_join_fk_is_null": q_left_fk,
            "left_join_nullable_nonkey_is_null": q_left_nullable_nonkey,
            "etm_rule25_not_in_rewrite": q_etm_rule25_rewrite,
            "safe_not_exists": q_safe_not_exists,
        },
        "chasm_trap_sqlite": {
            "true_invoice_sum": true_invoice_sum,
            "naive_multi_join_sum": naive_sum,
            "grain_fanout_ratio": fanout_ratio,
            "cte_pre_aggregated_sum": guarded_cte_sum,
        },
        "spider2_evaluate_sqlite": {
            "gold_spider2lite_ignore_order_true": "547/547 (100.0%, 463/547 multi-col)",
            "gold_spider2snow_ignore_order_true": "547/547 (100.0%)",
            "gold_spider2dbt_ignore_orders_all_true": "68/68 (100.0%, duckdb_match)",
            "corrupted_sql_spider2_score": spider2_corrupted_score,
            "corrupted_sql_sound_score": sound_corrupted_score,
            "reordered_valid_sql_sound_score": sound_reordered_valid_score,
            "exp_boundary_0p999999_vs_1p000001_sound_score": sound_exp_boundary_pos_ctrl,
            "near_tie_bipartite_sound_score": sound_near_tie_bipartite_pos_ctrl,
            "swapped_binding_sound_score_nc": sound_swapped_binding_neg_ctrl,
        },
        "chase_sql_alg3": {
            "exp_score_wrong_member_ordered_i_ne_j": round(exp_wrong_ordered, 4),
            "exp_score_singleton_correct_ordered_i_ne_j": round(exp_cstar_ordered, 4),
            "exp_score_wrong_leader_unordered_asym": round(exp_c0_unordered_asym, 4),
            "exp_score_wrong_member_unordered_sym_nc": round(exp_c_unordered_sym_nc, 4),
            "exp_score_singleton_correct_unordered": round(exp_cstar_unordered, 4),
            "critical_m_unordered_flash_p07101": round(crit_m_unordered_flash, 2),
            "critical_m_unordered_sonnet_p06021": round(crit_m_unordered_sonnet, 2),
            "ordered_copeland_dedup_winner": dedup_ordered_winner,
            "ordered_copeland_cloned_B_winner": cloned_ordered_winner,
            "cloned_B_dedup_bradley_terry_winner": cloned_dedup_bt_winner,
            "ordered_alg3_238calls_first_tie_win_rate": round(r_ord_first, 4),
            "ordered_alg3_238calls_win_rate": round(r_ord_fair, 4),
            "unordered_asym_119calls_first_tie_win_rate": round(r_asym_first, 4),
            "unordered_asym_119calls_win_rate": round(r_asym, 4),
            "unordered_sym_nc_119calls_win_rate": round(r_sym, 4),
            "cluster_dedup_1vote_28calls_win_rate": round(r_dedup1, 4),
            "cluster_dedup_3vote_84calls_win_rate": round(r_dedup3, 4),
            "cluster_dedup_7vote_maj_196calls_win_rate": round(r_dedup7_maj, 4),
            "cluster_dedup_7vote_bradley_terry_196calls_win_rate": round(r_dedup7_bt, 4),
        },
    }


# ===========================================================================
# Probe 2: CHESS preprocess.py & retrieve_entity.py Exact LSH Reproduction
# ===========================================================================
def run_probe_p2() -> dict:
    # Exact reproduction of ShayanTalaei/CHESS@3d6e835f858d26885d21d4bc0215aeecf855efbe:
    # - src/database_utils/db_values/preprocess.py:40 (raw substring filter + endswith("Id"))
    # - src/database_utils/db_values/preprocess.py:87-90 (_create_minhash n_gram=3)
    # - run/run_preprocess.sh:6-8 & search.py:49,67 (signature_size=100, n_gram=3, top_n=10)
    # - src/workflow/agents/information_retriever/tool_kit/retrieve_entity.py:257,268-275 (SequenceMatcher)
    chess_skip_keywords = [
        "_id", " id", "url", "email", "web", "time", "phone", "date", "address"
    ]

    def chess_keep_column(column: str) -> bool:
        if (
            any(keyword in column.lower() for keyword in chess_skip_keywords)
            or column.endswith("Id")
        ):
            return False
        return True

    skip_token_re = re.compile(
        r"(?:^|_|\s)(?:id|url|email|web|timestamp|phone|address)(?:$|_|\s)|[a-z0-9]Id$"
    )

    def fixed_keep_column(column: str) -> bool:
        return not bool(skip_token_re.search(column))

    MAX_HASH = (1 << 32) - 1
    sig_cache: dict[tuple[tuple[str, ...], int], tuple[int, ...]] = {}

    def minhash_signature(shingles: list[str], signature_size: int = 100) -> tuple[int, ...]:
        if not shingles:
            return (MAX_HASH,) * signature_size
        uniq_s = tuple(sorted(set(shingles)))
        ck = (uniq_s, signature_size)
        if ck in sig_cache:
            return sig_cache[ck]
        sig = [
            min(
                struct.unpack(
                    "<I", hashlib.blake2b(f"{perm}:{s}".encode("utf-8"), digest_size=4).digest()
                )[0]
                for s in uniq_s
            )
            for perm in range(signature_size)
        ]
        res = tuple(sig)
        sig_cache[ck] = res
        return res

    def chess_shingles_3gram(string: str, n_gram: int = 3) -> list[str]:
        return [string[i : i + n_gram] for i in range(len(string) - n_gram + 1)]

    def fixed_padded_multigram_shingles(string: str) -> list[str]:
        s = f"^{string.strip().lower()}$"
        return [s[i : i + n] for n in (1, 2, 3) for i in range(max(0, len(s) - n + 1))]

    def jaccard_est(s1: tuple[int, ...], s2: tuple[int, ...]) -> float:
        return sum(a == b for a, b in zip(s1, s2)) / len(s1)

    us_states_50 = [
        "AL", "AK", "AZ", "AR", "CA", "CO", "CT", "DE", "FL", "GA",
        "HI", "ID", "IL", "IN", "IA", "KS", "KY", "LA", "ME", "MD",
        "MA", "MI", "MN", "MS", "MO", "MT", "NE", "NV", "NH", "NJ",
        "NM", "NY", "NC", "ND", "OH", "OK", "OR", "PA", "RI", "SC",
        "SD", "TN", "TX", "UT", "VT", "VA", "WA", "WV", "WI", "WY",
    ]
    tax_classes_12 = ["A", "B", "C", "D", "E", "F", "G", "H", "M", "S", "W", "X"]

    business_substring_cols = {
        "candidate_status": ["Active", "Withdrawn", "Elected", "Disqualified"],
        "mandate_type": ["SEPA_CORE", "SEPA_B2B", "ACH_DEBIT"],
        "full_time_band": ["FT_REGULAR", "PT_SEASONAL", "CONTRACTOR"],
        "overtime_policy": ["EXEMPT", "NON_EXEMPT_1_5X", "DOUBLE_TIME"],
        "multimedia_format": ["MP4_HDR", "WEBM_VP9", "WAV_PCM"],
    }
    schema_values = {
        "state_code": us_states_50,
        "tax_class": tax_classes_12,
        **business_substring_cols,
        # True ID / contact columns that BOTH filters must reject (negative control):
        "user_id": ["u_1001", "u_1002"],
        "merchantId": ["m_900", "m_901"],
        "email_address": ["a@b.org", "c@d.org"],
    }

    chess_index = [
        (f"tbl_{col}_{idx}", minhash_signature(chess_shingles_3gram(val, 3), 100), col, val)
        for col, vals in schema_values.items()
        if chess_keep_column(col)
        for idx, val in enumerate(vals)
    ]
    fixed_index = [
        (f"tbl_{col}_{idx}", minhash_signature(fixed_padded_multigram_shingles(val), 100), col, val)
        for col, vals in schema_values.items()
        if fixed_keep_column(col)
        for idx, val in enumerate(vals)
    ]

    short_sigs = [sig for _, sig, _, val in chess_index if len(val) < 3]
    assert len(short_sigs) == 62
    assert len(set(short_sigs)) == 1 and short_sigs[0] == (MAX_HASH,) * 100

    def run_chess_lsh_plus_edit_rerank(index, shingle_fn, query_str: str, top_n: int = 10):
        q_sig = minhash_signature(shingle_fn(query_str), 100)
        above_thresh = [
            (key, jac, col, val)
            for key, sig, col, val in index
            if (jac := jaccard_est(q_sig, sig)) >= 0.01
        ]
        above_thresh.sort(key=lambda x: x[1], reverse=True)
        top_lsh = above_thresh[:top_n]
        q_low = query_str.lower()
        reranked = []
        for _, jac, col, val in top_lsh:
            sim = SequenceMatcher(None, q_low, val.lower()).ratio()
            if sim >= 0.3:
                reranked.append((sim, jac, col, val))
        reranked.sort(key=lambda x: (x[0], x[1]), reverse=True)
        return top_lsh, reranked

    # 1. Exhaustive uniform evaluation across ALL 62 <3-char short codes (no tail cherry-picking):
    # Under top_n=10 over 62 identical all-MAX_HASH vectors, exactly 10/62 = 16.13% survive LSH
    # (in live datasketch.MinHashLSH, set iteration order depends on PYTHONHASHSEED, with uniform
    # expectation 10/62 = 0.1613).
    all_short_queries = [("state_code", s) for s in us_states_50] + [
        ("tax_class", c) for c in tax_classes_12
    ]
    chess_short_hits = sum(
        1
        for col, val in all_short_queries
        for _, rerank in [run_chess_lsh_plus_edit_rerank(chess_index, chess_shingles_3gram, val, 10)]
        if rerank and (rerank[0][2], rerank[0][3]) == (col, val)
    )
    fixed_short_hits = sum(
        1
        for col, val in all_short_queries
        for _, rerank in [
            run_chess_lsh_plus_edit_rerank(fixed_index, fixed_padded_multigram_shingles, val, 10)
        ]
        if rerank and (rerank[0][2], rerank[0][3]) == (col, val)
    )

    # 2. Exhaustive evaluation across ALL 16 values in the 5 substring-blacklisted business columns:
    all_dropped_col_queries = [
        (col, val) for col, vals in business_substring_cols.items() for val in vals
    ]
    chess_dropped_col_hits = sum(
        1
        for col, val in all_dropped_col_queries
        for _, rerank in [run_chess_lsh_plus_edit_rerank(chess_index, chess_shingles_3gram, val, 10)]
        if rerank and (rerank[0][2], rerank[0][3]) == (col, val)
    )
    fixed_dropped_col_hits = sum(
        1
        for col, val in all_dropped_col_queries
        for _, rerank in [
            run_chess_lsh_plus_edit_rerank(fixed_index, fixed_padded_multigram_shingles, val, 10)
        ]
        if rerank and (rerank[0][2], rerank[0][3]) == (col, val)
    )

    dropped_business_cols = [c for c in business_substring_cols if not chess_keep_column(c)]
    kept_id_cols_fixed = [
        c for c in ["user_id", "merchantId", "email_address"] if fixed_keep_column(c)
    ]
    assert len(dropped_business_cols) == 5
    assert kept_id_cols_fixed == []
    assert chess_short_hits == 10 and len(all_short_queries) == 62
    assert fixed_short_hits == 62
    assert chess_dropped_col_hits == 0 and fixed_dropped_col_hits == len(all_dropped_col_queries)

    return {
        "dropped_business_columns": dropped_business_cols,
        "distinct_minhash_vectors_across_62_short_codes_chess": len(set(short_sigs)),
        "short_codes_truncated_by_top10_lsh_pct": round(100.0 * (62 - 10) / 62, 2),
        "uniform_62_short_code_recall_chess": round(chess_short_hits / len(all_short_queries), 4),
        "uniform_62_short_code_recall_fixed": round(fixed_short_hits / len(all_short_queries), 4),
        "substring_dropped_col_recall_chess": round(
            chess_dropped_col_hits / len(all_dropped_col_queries), 4
        ),
        "substring_dropped_col_recall_fixed": round(
            fixed_dropped_col_hits / len(all_dropped_col_queries), 4
        ),
        "fixed_false_indexed_id_cols_nc": len(kept_id_cols_fixed),
    }


# ===========================================================================
# Probe 3: AIDE journal.py _metric_rank Bug & De-Confounded GroupKFold Search
# ===========================================================================
def run_probe_p3() -> dict:
    # Probe 3a. [exact reproduction of pinned SQL/evaluator logic]
    # WecoAI/aideml@ad73d227af481bea3de06f884f41b2993dd6453a aide/journal.py:162-228
    class AideMetricValue:
        def __init__(self, value: float | None, maximize: bool | None, is_worst: bool = False):
            self.value = value
            self.maximize = maximize
            self.is_worst = is_worst

    class AideNode:
        def __init__(self, node_id: str, metric: AideMetricValue, is_buggy: bool = False):
            self.id = node_id
            self.metric = metric
            self.is_buggy = is_buggy

    class AideJournal:
        def __init__(self, metric_maximize: bool | None = None):
            self.nodes: list[AideNode] = []
            self.metric_maximize = metric_maximize
            self.warnings: list[str] = []

        def _reconcile_metric_directions(self) -> None:
            metrics = [
                n.metric for n in self.nodes if n.metric is not None and not n.metric.is_worst
            ]
            if self.metric_maximize is None:
                self.metric_maximize = next(
                    (m.maximize for m in metrics if m.maximize is not None), None
                )

        def _warn_on_direction_conflict(self, metric: AideMetricValue | None) -> None:
            if (
                metric is not None
                and not metric.is_worst
                and self.metric_maximize is not None
                and metric.maximize is not None
                and metric.maximize != self.metric_maximize
            ):
                self.warnings.append(
                    f"Metric direction {metric.maximize} disagrees with journal direction {self.metric_maximize}"
                )

        def _metric_rank(self, metric: AideMetricValue | None) -> tuple[bool, float]:
            if metric is None or metric.is_worst:
                return False, 0.0
            assert metric.value is not None
            val = float(metric.value)
            return True, val if self.metric_maximize else -val

        def append(self, node: AideNode) -> None:
            self.nodes.append(node)
            self._reconcile_metric_directions()
            self._warn_on_direction_conflict(node.metric)

        def get_best_node(self) -> AideNode | None:
            self._reconcile_metric_directions()
            good = [n for n in self.nodes if not n.is_buggy]
            if not good:
                return None
            return max(good, key=lambda n: self._metric_rank(n.metric))

    j_min = AideJournal(metric_maximize=False)
    j_min.append(AideNode("good_rmse_0p34", AideMetricValue(0.34, maximize=False)))
    j_min.append(AideNode("broken_r2_neg0p25", AideMetricValue(-0.25, maximize=True)))
    picked_min = j_min.get_best_node()

    j_max = AideJournal(metric_maximize=True)
    j_max.append(AideNode("good_auc_0p86", AideMetricValue(0.86, maximize=True)))
    j_max.append(AideNode("bad_rmse_1p45", AideMetricValue(1.45, maximize=False)))
    picked_max = j_max.get_best_node()

    assert picked_min is not None and picked_min.id == "broken_r2_neg0p25"
    assert len(j_min.warnings) == 1
    assert picked_max is not None and picked_max.id == "bad_rmse_1p45"

    # Probe 3b. [toy model / controlled tabular experiment]
    # De-confounded grouped-entity Ridge regression tree search (general adaptive holdout sample
    # complexity is established in corpus report
    # `reusable-holdout-thresholdout-ladder-leaderboards-and-clopper-pearson-zero-numerators`).
    # Isolates:
    #   (1) Random row split (`50/50` 120-row fit + matched 192-row refit, and `80/20` 192-row fit);
    #   (2) Pure unpenalized greedy 4-fold `GroupKFold` (`192` rows + `48`-row Lockbox):
    #       On disjoint validation entities, `z_ent == 0.0`, eliminating validation target leakage
    #       (`90.0% -> 5.0%` z_ent selection; `clean = 0.3841`). Notably, `z_ent` does NOT strictly
    #       worsen OOF R^2 in 100% of trials (`1/20 = 5.0%` selected, `test_r2 = 0.3623`), because on
    #       training folds `z_ent` acts as a regularized Frisch-Waugh-Lovell entity fixed-effect
    #       nuisance absorber against sigma_u = 1.50 random intercepts!
    #   (3) Complexity-penalized (`-0.004 * len(act)`) greedy `GroupKFold` (`0.0%` hijack, `0.3846`);
    #   (4) Full guarded `GroupKFold` + `-0.004 * len(act)` + top-3 beam (`0.0%` hijack, `0.3877`).
    n_trials = 20
    d_sig = 4
    d_total = 24
    T = 85
    num_drafts = 5
    k_max = 8

    def make_grouped_dataset(rng_d: random.Random, n_entities: int, rows_per_ent: int = 2):
        X, g_ids, y = [], [], []
        for g in range(n_entities):
            u_g = rng_d.gauss(0.0, 1.50)
            for _ in range(rows_per_ent):
                row = [rng_d.gauss(0.0, 1.0) for _ in range(d_total)]
                val = 0.72 * sum(row[:d_sig]) + u_g + rng_d.gauss(0.0, 0.60)
                X.append(row)
                g_ids.append(g)
                y.append(val)
        return X, g_ids, y

    def centered_ent_map(g_fit: list[int], y_fit: list[float]) -> dict[int, float]:
        mu = sum(y_fit) / len(y_fit)
        by_g: dict[int, list[float]] = {}
        for g, yv in zip(g_fit, y_fit):
            by_g.setdefault(g, []).append(yv)
        return {g: (sum(vs) / len(vs)) - mu for g, vs in by_g.items()}

    def precompute_moments(
        X_rows: list[list[float]], y_rows: list[float], z_cols: list[list[float]]
    ) -> dict:
        n_r = len(y_rows)
        aug = [X_rows[i] + [zc[i] for zc in z_cols] for i in range(n_r)]
        m_dim = len(aug[0])
        inv_n = 1.0 / n_r
        G = [[0.0] * m_dim for _ in range(m_dim)]
        rhs_raw = [0.0] * m_dim
        col_mean = [0.0] * m_dim
        mu_y = sum(y_rows) * inv_n
        y2 = sum(yv * yv for yv in y_rows) * inv_n
        var_y = y2 - mu_y * mu_y
        for i in range(n_r):
            r = aug[i]
            yv = y_rows[i]
            for a in range(m_dim):
                ra = r[a]
                col_mean[a] += ra
                rhs_raw[a] += ra * yv
                Ga = G[a]
                for b in range(a, m_dim):
                    Ga[b] += ra * r[b]
        for a in range(m_dim):
            col_mean[a] *= inv_n
            rhs_raw[a] = rhs_raw[a] * inv_n - col_mean[a] * mu_y
            for b in range(a, m_dim):
                G[a][b] *= inv_n
                G[b][a] = G[a][b]
        C = [
            [G[a][b] - col_mean[a] * col_mean[b] for b in range(m_dim)] for a in range(m_dim)
        ]
        rhs_unc = [rhs_raw[a] + col_mean[a] * mu_y for a in range(m_dim)]
        return {
            "G": G,
            "C": C,
            "rhs_c": rhs_raw,
            "rhs_unc": rhs_unc,
            "col_mean": col_mean,
            "mu_y": mu_y,
            "y2": y2,
            "var_y": var_y,
        }

    def solve_small_linear(A: list[list[float]], b_vec: list[float]) -> list[float]:
        m = len(b_vec)
        M = [row + [b_vec[i]] for i, row in enumerate(A)]
        m1 = m + 1
        for col in range(m):
            piv = col
            best_abs = abs(M[col][col])
            for r in range(col + 1, m):
                v_abs = abs(M[r][col])
                if v_abs > best_abs:
                    best_abs = v_abs
                    piv = r
            if piv != col:
                M[col], M[piv] = M[piv], M[col]
            piv_row = M[col]
            div = piv_row[col]
            for j in range(col, m1):
                piv_row[j] /= div
            for r in range(m):
                if r != col:
                    row_r = M[r]
                    fac = row_r[col]
                    if fac != 0.0:
                        for j in range(col, m1):
                            row_r[j] -= fac * piv_row[j]
        return [M[i][m] for i in range(m)]

    def eval_r2_fast(
        tr_m: dict, ev_m: dict, active_idx: tuple[int, ...], l2: float = 0.15
    ) -> float:
        m = len(active_idx)
        C_tr, cm_tr, mu_tr, rhs_tr = tr_m["C"], tr_m["col_mean"], tr_m["mu_y"], tr_m["rhs_c"]
        sub_A = []
        b_sub = []
        for a, ia in enumerate(active_idx):
            Ca = C_tr[ia]
            row_a = [Ca[ib] for ib in active_idx]
            row_a[a] += l2
            sub_A.append(row_a)
            b_sub.append(rhs_tr[ia])
        w = solve_small_linear(sub_A, b_sub)
        b0 = mu_tr - sum(w[a] * cm_tr[active_idx[a]] for a in range(m))
        G_ev, cm_ev, mu_ev, y2_ev, rhs_u = (
            ev_m["G"],
            ev_m["col_mean"],
            ev_m["mu_y"],
            ev_m["y2"],
            ev_m["rhs_unc"],
        )
        wt_x_y = 0.0
        wt_cm = 0.0
        wt_G_w = 0.0
        for a, ia in enumerate(active_idx):
            wa = w[a]
            wt_x_y += wa * rhs_u[ia]
            wt_cm += wa * cm_ev[ia]
            Ga_ev = G_ev[ia]
            for b, ib in enumerate(active_idx):
                wt_G_w += wa * Ga_ev[ib] * w[b]
        mse = (y2_ev - 2.0 * b0 * mu_ev + b0 * b0) - 2.0 * (wt_x_y - b0 * wt_cm) + wt_G_w
        return 1.0 - mse / ev_m["var_y"]

    def mutate_subset(
        rng_s: random.Random,
        cols: tuple[int, ...],
        leak_mode: int,
        allow_leak_ops: bool,
    ) -> tuple[tuple[int, ...], int]:
        c_list = list(cols)
        if allow_leak_ops and rng_s.random() < 0.055:
            leak_mode = 2 if rng_s.random() < 0.45 else max(leak_mode, 1)
            if len(c_list) >= k_max:
                c_list.pop(rng_s.randrange(len(c_list)))
        else:
            cap = (k_max - 1) if leak_mode > 0 else k_max
            j = rng_s.randrange(d_total)
            if j in c_list and len(c_list) > 1 and rng_s.random() < 0.35:
                c_list.remove(j)
            elif j not in c_list:
                if len(c_list) >= cap and c_list:
                    c_list[rng_s.randrange(len(c_list))] = j
                else:
                    c_list.append(j)
        return tuple(sorted(set(c_list))), leak_mode

    configs = [
        # (arm_key, allow_leak, split_kind, use_beam3, l0_pen, refit_192)
        ("clean_raw_aide_120fit", False, "rand50", False, 0.0, False),
        ("clean_raw_aide_192refit", False, "rand50", False, 0.0, True),
        ("clean_rand80_20_192fit", False, "rand80", False, 0.0, False),
        ("clean_pure_greedy_group_oof_192fit", False, "group_oof", False, 0.0, True),
        ("clean_greedy_penalized_group_oof_192fit", False, "group_oof", False, 0.004, True),
        ("clean_full_guarded_group_oof_192fit", False, "group_oof", True, 0.004, True),
        ("leak_raw_aide_120fit", True, "rand50", False, 0.0, False),
        ("leak_raw_aide_192refit", True, "rand50", False, 0.0, True),
        ("leak_rand80_20_192fit", True, "rand80", False, 0.0, False),
        ("leak_pure_greedy_group_oof_192fit", True, "group_oof", False, 0.0, True),
        ("leak_greedy_penalized_group_oof_192fit", True, "group_oof", False, 0.004, True),
        ("leak_full_guarded_group_oof_192fit", True, "group_oof", True, 0.004, True),
    ]
    arms: dict[str, list[dict]] = {c[0]: [] for c in configs}

    for ti in range(n_trials):
        rng_d = random.Random(SEED + ti * 1009)
        X_lab, g_lab, y_lab = make_grouped_dataset(rng_d, n_entities=120, rows_per_ent=2)
        X_te, _, y_te = make_grouped_dataset(rng_d, n_entities=200, rows_per_ent=2)
        m_te = precompute_moments(X_te, y_te, [[0.0] * len(y_te), [0.0] * len(y_te)])

        rng_sp = random.Random(770000 + ti * 97)
        idx_all = list(range(len(y_lab)))
        rng_sp.shuffle(idx_all)
        tr_idx, va_idx = idx_all[:120], idx_all[120:]
        X_tr = [X_lab[i] for i in tr_idx]
        g_tr = [g_lab[i] for i in tr_idx]
        y_tr = [y_lab[i] for i in tr_idx]
        X_va = [X_lab[i] for i in va_idx]
        g_va = [g_lab[i] for i in va_idx]
        y_va = [y_lab[i] for i in va_idx]
        em_sp = centered_ent_map(g_tr, y_tr)
        em_pre = centered_ent_map(g_lab, y_lab)
        m_tr = precompute_moments(
            X_tr, y_tr, [[em_sp.get(g, 0.0) for g in g_tr], [em_pre.get(g, 0.0) for g in g_tr]]
        )
        m_va = precompute_moments(
            X_va, y_va, [[em_sp.get(g, 0.0) for g in g_va], [em_pre.get(g, 0.0) for g in g_va]]
        )

        # Matched 192-row random 80/20 split (isolates row count 192 vs entity-grouped splitting)
        tr80_idx, va20_idx = idx_all[:192], idx_all[192:]
        X_tr80 = [X_lab[i] for i in tr80_idx]
        g_tr80 = [g_lab[i] for i in tr80_idx]
        y_tr80 = [y_lab[i] for i in tr80_idx]
        X_va20 = [X_lab[i] for i in va20_idx]
        g_va20 = [g_lab[i] for i in va20_idx]
        y_va20 = [y_lab[i] for i in va20_idx]
        em_sp80 = centered_ent_map(g_tr80, y_tr80)
        m_tr80 = precompute_moments(
            X_tr80,
            y_tr80,
            [[em_sp80.get(g, 0.0) for g in g_tr80], [em_pre.get(g, 0.0) for g in g_tr80]],
        )
        m_va20 = precompute_moments(
            X_va20,
            y_va20,
            [[em_sp80.get(g, 0.0) for g in g_va20], [em_pre.get(g, 0.0) for g in g_va20]],
        )

        X_cv, g_cv, y_cv = X_lab[:192], g_lab[:192], y_lab[:192]
        X_lk, _, y_lk = X_lab[192:], g_lab[192:], y_lab[192:]
        folds = []
        for f in range(4):
            s, e = f * 48, (f + 1) * 48
            Xf = X_cv[:s] + X_cv[e:]
            gf = g_cv[:s] + g_cv[e:]
            yf = y_cv[:s] + y_cv[e:]
            emf = centered_ent_map(gf, yf)
            zf = [emf.get(g, 0.0) for g in gf]
            yfv = y_cv[s:e]
            folds.append(
                (
                    precompute_moments(Xf, yf, [zf, zf]),
                    precompute_moments(X_cv[s:e], yfv, [[0.0] * len(yfv), [0.0] * len(yfv)]),
                )
            )
        em_cv = centered_ent_map(g_cv, y_cv)
        z_cv = [em_cv.get(g, 0.0) for g in g_cv]
        m_cv = precompute_moments(X_cv, y_cv, [z_cv, z_cv])
        m_lk = precompute_moments(X_lk, y_lk, [[0.0] * len(y_lk), [0.0] * len(y_lk)])

        val_cache: dict[tuple[str, tuple[int, ...]], float] = {}

        def cached_split_r2(split_kind: str, act: tuple[int, ...]) -> float:
            ck = (split_kind, act)
            if ck in val_cache:
                return val_cache[ck]
            if split_kind == "rand50":
                v = eval_r2_fast(m_tr, m_va, act)
            elif split_kind == "rand80":
                v = eval_r2_fast(m_tr80, m_va20, act)
            else:
                v = sum(eval_r2_fast(mtr_f, mva_f, act) for mtr_f, mva_f in folds) / 4.0
            val_cache[ck] = v
            return v

        search_runs = [
            # (search_arms, allow_lk, split_kind, use_beam3, l0_pen)
            ([("clean_raw_aide_120fit", False), ("clean_raw_aide_192refit", True)], False, "rand50", False, 0.0),
            ([("clean_rand80_20_192fit", False)], False, "rand80", False, 0.0),
            ([("clean_pure_greedy_group_oof_192fit", True)], False, "group_oof", False, 0.0),
            ([("clean_greedy_penalized_group_oof_192fit", True)], False, "group_oof", False, 0.004),
            ([("clean_full_guarded_group_oof_192fit", True)], False, "group_oof", True, 0.004),
            ([("leak_raw_aide_120fit", False), ("leak_raw_aide_192refit", True)], True, "rand50", False, 0.0),
            ([("leak_rand80_20_192fit", False)], True, "rand80", False, 0.0),
            ([("leak_pure_greedy_group_oof_192fit", True)], True, "group_oof", False, 0.0),
            ([("leak_greedy_penalized_group_oof_192fit", True)], True, "group_oof", False, 0.004),
            ([("leak_full_guarded_group_oof_192fit", True)], True, "group_oof", True, 0.004),
        ]

        for target_arms, allow_lk, split_kind, use_beam3, l0_pen in search_runs:
            rng_s = random.Random(880000 + ti * 131)
            nodes = []
            for step in range(1, T + 1):
                if step <= num_drafts:
                    cols = tuple(sorted(rng_s.sample(range(d_total), 2)))
                    lm = 0
                else:
                    if use_beam3:
                        top_pool = sorted(nodes, key=lambda nd: nd["sel"], reverse=True)[:3]
                        parent = top_pool[step % len(top_pool)]
                    else:
                        parent = max(nodes, key=lambda nd: nd["sel"])
                    cols, lm = mutate_subset(rng_s, parent["cols"], parent["lm"], allow_lk)
                act = cols + ((d_total - 1 + lm,) if lm > 0 else ())
                v_r2 = cached_split_r2(split_kind, act)
                nodes.append(
                    {"cols": cols, "lm": lm, "act": act, "val": v_r2, "sel": v_r2 - l0_pen * len(act)}
                )
            best = max(nodes, key=lambda nd: nd["sel"])
            for arm_key, refit_192 in target_arms:
                if split_kind == "rand50":
                    fit_m = m_tr80 if refit_192 else m_tr
                    te_r2 = eval_r2_fast(fit_m, m_te, best["act"])
                    rep_gap = best["val"] - te_r2
                elif split_kind == "rand80":
                    te_r2 = eval_r2_fast(m_tr80, m_te, best["act"])
                    rep_gap = best["val"] - te_r2
                else:
                    lk_r2 = eval_r2_fast(m_cv, m_lk, best["act"])
                    te_r2 = eval_r2_fast(m_cv, m_te, best["act"])
                    rep_gap = lk_r2 - te_r2
                arms[arm_key].append(
                    {"test_r2": te_r2, "report_gap": rep_gap, "z_ent_selected": best["lm"] > 0}
                )

    def summarize_arm(key: str) -> dict:
        arr = arms[key]
        return {
            "test_r2": round(statistics.mean(x["test_r2"] for x in arr), 4),
            "report_gap": round(statistics.mean(x["report_gap"] for x in arr), 4),
            "z_ent_select_rate": round(sum(x["z_ent_selected"] for x in arr) / n_trials, 4),
        }

    g_summary = {c[0]: summarize_arm(c[0]) for c in configs}
    assert math.isclose(g_summary["clean_pure_greedy_group_oof_192fit"]["test_r2"], 0.3841)
    assert (
        g_summary["clean_pure_greedy_group_oof_192fit"]["test_r2"]
        > g_summary["clean_raw_aide_192refit"]["test_r2"]
        > g_summary["clean_rand80_20_192fit"]["test_r2"]
    )
    assert g_summary["leak_raw_aide_120fit"]["z_ent_select_rate"] == 0.90
    assert g_summary["leak_rand80_20_192fit"]["z_ent_select_rate"] == 0.85
    # Pure unpenalized GroupKFold drops hijack 90% -> 5% (1/20 FWL demeaning), and l0_pen -> 0.0%
    assert g_summary["leak_pure_greedy_group_oof_192fit"]["z_ent_select_rate"] == 0.05
    assert g_summary["leak_greedy_penalized_group_oof_192fit"]["z_ent_select_rate"] == 0.0
    assert g_summary["leak_full_guarded_group_oof_192fit"]["z_ent_select_rate"] == 0.0
    assert (
        g_summary["leak_full_guarded_group_oof_192fit"]["test_r2"]
        - g_summary["leak_raw_aide_192refit"]["test_r2"]
        > 0.08
    )

    return {
        "aide_journal_direction_bug": {
            "minimize_rmse_selected_node": picked_min.id,
            "maximize_auc_selected_node": picked_max.id,
            "logged_warnings_without_rejection": len(j_min.warnings),
        },
        "grouped_tabular_tree_search": g_summary,
    }


# ===========================================================================
# Probe 4: DiscoveryBench new_eval.py Bugs & BLADE Multiverse Lockbox Ablation
# ===========================================================================
def norm_cdf(x: float) -> float:
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def two_sided_p_from_z(z: float) -> float:
    return 2.0 * (1.0 - norm_cdf(abs(z)))


def run_probe_p4() -> dict:
    # Probe 4a. [exact reproduction of pinned SQL/evaluator logic] + [exact analytical / derived calculation]
    # allenai/discoverybench@c31fcf011e070f021a5f5b906896d0821f6880e8
    # discovery_eval.py:3 -> eval/new_eval.py:386-435 vs. arXiv:2407.01725v1 Sec. 4.3 (p. 7, L471).
    def discoverybench_eval_repro(
        gold_subhs: list[dict], gen_subhs: list[dict], pass_unsegmented_bug: bool = True
    ) -> dict:
        full_gold_vars = sorted({v for sh in gold_subhs for v in sh["vars"]})
        full_gen_vars = sorted({v for sh in gen_subhs for v in sh["vars"]})

        gold_covered: list[int] = []
        gen_to_gold: dict[int, int] = {}
        for p_id, gen_sh in enumerate(gen_subhs):
            gen_to_gold[p_id] = -1
            for g_id, gold_sh in enumerate(gold_subhs):
                if g_id in gold_covered:
                    continue
                if gen_sh["ctx"] == gold_sh["ctx"]:
                    gen_to_gold[p_id] = g_id
                    gold_covered.append(g_id)
                    break

        sum_accuracy_score = 0.0
        for p_id, g_id in gen_to_gold.items():
            if g_id >= 0:
                g_vars = set(full_gold_vars if pass_unsegmented_bug else gold_subhs[g_id]["vars"])
                p_vars = set(full_gen_vars if pass_unsegmented_bug else gen_subhs[p_id]["vars"])
                inter = len(g_vars & p_vars)
                var_f1 = (2.0 * inter / (len(g_vars) + len(p_vars))) if (g_vars or p_vars) else 0.0
                rel_sc = 1.0 if gen_subhs[p_id]["rel"] == gold_subhs[g_id]["rel"] else 0.0
                sum_accuracy_score += 1.0 * var_f1 * rel_sc

        n_g, m_p, n_m = len(gold_subhs), len(gen_subhs), len(gold_covered)
        recall_ctx = n_m / n_g if n_g else 0.0
        mean_acc = sum_accuracy_score / m_p if m_p else 0.0
        deployed_final_score = recall_ctx * mean_acc

        ctx_f1 = (2.0 * n_m / (n_g + m_p)) if (n_g + m_p) else 0.0
        bar_s = (sum_accuracy_score / n_m) if n_m else 0.0
        paper_hms = ctx_f1 * bar_s
        return {
            "deployed_score": round(deployed_final_score, 4),
            "paper_hms": round(paper_hms, 4),
            "ratio_paper_over_deployed": round(paper_hms / deployed_final_score, 4)
            if deployed_final_score > 0
            else None,
        }

    gold_4 = [
        {"ctx": "c1", "vars": ["age", "income"], "rel": "pos"},
        {"ctx": "c2", "vars": ["age", "income"], "rel": "pos"},
        {"ctx": "c3", "vars": ["age", "income"], "rel": "pos"},
        {"ctx": "c4", "vars": ["age", "income"], "rel": "pos"},
    ]
    pred_4_half = [
        {"ctx": "c1", "vars": ["age", "income"], "rel": "pos"},
        {"ctx": "c2", "vars": ["age", "income"], "rel": "pos"},
        {"ctx": "c_wrong1", "vars": ["age", "income"], "rel": "pos"},
        {"ctx": "c_wrong2", "vars": ["age", "income"], "rel": "pos"},
    ]
    hms_half = discoverybench_eval_repro(gold_4, pred_4_half, pass_unsegmented_bug=False)
    hms_full_nc = discoverybench_eval_repro(gold_4, gold_4, pass_unsegmented_bug=False)
    gold_seg = [
        {"ctx": "men_u20", "vars": ["age", "income"], "rel": "pos"},
        {"ctx": "women_o40", "vars": ["bmi", "bp"], "rel": "pos"},
    ]
    pred_seg_swapped = [
        {"ctx": "men_u20", "vars": ["bmi", "bp"], "rel": "pos"},
        {"ctx": "unmatched_ctx", "vars": ["age", "income"], "rel": "pos"},
    ]
    unseg_leak = discoverybench_eval_repro(gold_seg, pred_seg_swapped, pass_unsegmented_bug=True)
    seg_clean = discoverybench_eval_repro(gold_seg, pred_seg_swapped, pass_unsegmented_bug=False)

    assert math.isclose(hms_half["paper_hms"], 0.50) and math.isclose(
        hms_half["deployed_score"], 0.25
    )
    assert math.isclose(hms_full_nc["paper_hms"], 1.0) and math.isclose(
        hms_full_nc["deployed_score"], 1.0
    )
    assert unseg_leak["deployed_score"] == 0.25 and seg_clean["deployed_score"] == 0.0

    # Probe 4b. [toy model / controlled tabular experiment]
    # Multiverse p-hacking & specification-curve ablation across M = 48 branches
    # (6 subgroups x 8 correlated BLADE operationalizations, 1,000 runs) at both moderate (rho=0.60)
    # and high intra-subgroup correlation (rho=0.85), comparing single-spec Lockbox testing vs.
    # full Specification-Curve Lockbox confirmation (>=75% sign agreement + directional median p < alpha_s).
    n_sims = 1000
    n_subgroups = 6
    n_specs = 8
    M = n_subgroups * n_specs

    def eval_multiverse_suite(rho: float) -> dict:
        rng = random.Random(SEED)
        s_sh = math.sqrt(rho)
        s_id = math.sqrt(1.0 - rho)
        out_rho = {}

        for regime in ("null_pure_noise_h0", "null_single_spec_collider_h0", "alt_true_signal_h1"):
            c_naive = 0
            c_bh_single = 0
            c_split_bh_no_speccurve = 0
            c_single_spec_lockbox = 0
            c_speccurve_lockbox = 0

            for _ in range(n_sims):
                disc_p, disc_z, conf_z = [], [], []
                sg_disc_z = [[] for _ in range(n_subgroups)]
                sg_conf_z = [[] for _ in range(n_subgroups)]

                for sg in range(n_subgroups):
                    sh_d = rng.gauss(0.0, 1.0)
                    sh_c = rng.gauss(0.0, 1.0)
                    for sp in range(n_specs):
                        if regime == "alt_true_signal_h1" and sg == 0:
                            mu = 3.6
                        elif regime == "null_single_spec_collider_h0" and sg == 0 and sp == 0:
                            mu = 3.8
                        else:
                            mu = 0.0
                        zd = mu + s_sh * sh_d + s_id * rng.gauss(0.0, 1.0)
                        zc = mu + s_sh * sh_c + s_id * rng.gauss(0.0, 1.0)
                        disc_z.append((zd, sg))
                        conf_z.append((zc, sg))
                        disc_p.append(two_sided_p_from_z(zd))
                        sg_disc_z[sg].append(zd)
                        sg_conf_z[sg].append(zc)

                if min(disc_p) < 0.05:
                    c_naive += 1

                sp_sorted = sorted(disc_p)
                if any(p <= 0.05 * (i + 1) / M for i, p in enumerate(sp_sorted)):
                    c_bh_single += 1

                indexed = sorted(range(M), key=lambda k: disc_p[k])
                k_max = -1
                for rank, idx in enumerate(indexed):
                    if disc_p[idx] <= 0.10 * (rank + 1) / M:
                        k_max = rank
                bh_screened = [indexed[r] for r in range(k_max + 1)] if k_max >= 0 else []

                if bh_screened:
                    top_by_sg: dict[int, int] = {}
                    for idx in bh_screened:
                        top_by_sg.setdefault(disc_z[idx][1], idx)
                    t_list = list(top_by_sg.values())
                    alpha_c = 0.05 / len(t_list)
                    if any(
                        (conf_z[i][0] * disc_z[i][0] > 0)
                        and (two_sided_p_from_z(conf_z[i][0]) < alpha_c)
                        for i in t_list
                    ):
                        c_split_bh_no_speccurve += 1

                stable = []
                for idx in bh_screened:
                    zv, sg = disc_z[idx]
                    sgn = 1 if zv > 0 else -1
                    zs_sg = sg_disc_z[sg]
                    sign_agree = sum(1 for z_s in zs_sg if (1 if z_s > 0 else -1) == sgn) / n_specs
                    median_dir_z = statistics.median(sgn * z_s for z_s in zs_sg)
                    if sign_agree >= 0.75 and median_dir_z >= 1.645:
                        stable.append(idx)

                if stable:
                    top_st: dict[int, int] = {}
                    for idx in stable:
                        top_st.setdefault(disc_z[idx][1], idx)
                    s_list = list(top_st.values())
                    alpha_s = 0.05 / len(s_list)
                    # Single-spec Lockbox (vulnerable if sp=0 is the collider spec at high rho)
                    if any(
                        (conf_z[i][0] * disc_z[i][0] > 0)
                        and (two_sided_p_from_z(conf_z[i][0]) < alpha_s)
                        for i in s_list
                    ):
                        c_single_spec_lockbox += 1
                    # Full Spec-Curve Lockbox: confirm >=75% sign agreement + directional median p < alpha_s
                    if any(
                        (
                            sum(
                                1
                                for z_s in sg_conf_z[disc_z[i][1]]
                                if (1 if z_s > 0 else -1) == (1 if disc_z[i][0] > 0 else -1)
                            )
                            / n_specs
                            >= 0.75
                        )
                        and (
                            (
                                med_c := statistics.median(
                                    (1 if disc_z[i][0] > 0 else -1) * z_s
                                    for z_s in sg_conf_z[disc_z[i][1]]
                                )
                            )
                            > 0
                        )
                        and (two_sided_p_from_z(med_c) < alpha_s)
                        for i in s_list
                    ):
                        c_speccurve_lockbox += 1

            out_rho[regime] = {
                "naive_min_p_harking": round(c_naive / n_sims, 4),
                "bh_single_split_q005": round(c_bh_single / n_sims, 4),
                "split_bh_lockbox_no_speccurve": round(c_split_bh_no_speccurve / n_sims, 4),
                "single_spec_lockbox": round(c_single_spec_lockbox / n_sims, 4),
                "full_speccurve_lockbox": round(c_speccurve_lockbox / n_sims, 4),
            }
        return out_rho

    mv_rho60 = eval_multiverse_suite(0.60)
    mv_rho85 = eval_multiverse_suite(0.85)

    assert mv_rho60["null_pure_noise_h0"]["naive_min_p_harking"] > 0.70
    assert mv_rho60["null_pure_noise_h0"]["full_speccurve_lockbox"] <= 0.005
    assert mv_rho60["null_single_spec_collider_h0"]["split_bh_lockbox_no_speccurve"] > 0.70
    assert mv_rho60["null_single_spec_collider_h0"]["full_speccurve_lockbox"] == 0.0
    assert mv_rho85["null_single_spec_collider_h0"]["single_spec_lockbox"] == 0.045
    assert mv_rho85["null_single_spec_collider_h0"]["full_speccurve_lockbox"] == 0.002
    assert mv_rho60["alt_true_signal_h1"]["full_speccurve_lockbox"] >= 0.90
    assert mv_rho85["alt_true_signal_h1"]["full_speccurve_lockbox"] >= 0.85

    return {
        "discoverybench_new_eval_bugs": {
            "half_context_match_n4_m4_M2": hms_half,
            "full_context_match_negative_control": hms_full_nc,
            "unsegmented_hypo_var_leak_score": unseg_leak["deployed_score"],
            "segmented_subhypo_clean_score": seg_clean["deployed_score"],
        },
        "multiverse_48branch_ablation": {
            "rho_0p60": mv_rho60,
            "rho_0p85": mv_rho85,
        },
    }


# ===========================================================================
# Probe 5: DABstep SQLite Fee-Rule Fan-Out & BixBench graders.py Reproduction
# ===========================================================================
def run_probe_p5() -> dict:
    # Probe 5a. [toy model / controlled tabular experiment]
    # Controlled SQLite3 execution modeling DABstep operational payment fee-rule matching
    # (arXiv:2506.23719v1 Sec. 4.3 & App. A.4: static columns + wildcard NULLs + derived monthly tiers).
    conn = sqlite3.connect(":memory:")
    cur = conn.cursor()
    cur.executescript(
        """
        CREATE TABLE payments (
            tx_id INTEGER PRIMARY KEY,
            merchant TEXT NOT NULL,
            scheme TEXT NOT NULL,
            is_credit INTEGER NOT NULL,
            aci TEXT NOT NULL,
            eur_amount REAL NOT NULL,
            is_fraud INTEGER NOT NULL
        );
        CREATE TABLE fee_rules (
            rule_id INTEGER PRIMARY KEY,
            scheme TEXT NOT NULL,
            is_credit INTEGER NOT NULL,
            aci TEXT NULL,
            vol_tier TEXT NOT NULL,
            fraud_tier TEXT NOT NULL,
            rate_bps REAL NOT NULL
        );
        INSERT INTO payments VALUES
            (1, 'M_Alpha', 'Visa', 1, 'D', 100.0, 0),
            (2, 'M_Alpha', 'Visa', 1, 'D', 150.0, 0),
            (3, 'M_Alpha', 'Visa', 1, 'F', 900.0, 0),
            (4, 'M_Beta',  'Visa', 1, 'D',  80.0, 1),
            (5, 'M_Beta',  'Visa', 1, 'D', 120.0, 0);

        INSERT INTO fee_rules VALUES
            (10, 'Visa', 1, NULL, 'LOW_VOL',  'LOW_FRAUD',  190.0),
            (11, 'Visa', 1, NULL, 'HIGH_VOL', 'LOW_FRAUD',  110.0),
            (12, 'Visa', 1, NULL, 'LOW_VOL',  'HIGH_FRAUD', 320.0),
            (13, 'Visa', 1, NULL, 'HIGH_VOL', 'HIGH_FRAUD', 240.0);
        """
    )

    naive_on_clause = (
        "p.scheme = r.scheme AND p.is_credit = r.is_credit AND (r.aci IS NULL OR p.aci = r.aci)"
    )
    guarded_on_clause = (
        naive_on_clause + " AND m.vol_tier = r.vol_tier AND m.fraud_tier = r.fraud_tier"
    )
    rule_predicate_cols = {
        row[1]
        for row in cur.execute("PRAGMA table_info(fee_rules)")
        if row[1] not in {"rule_id", "rate_bps"}
    }
    unconsumed_naive = sorted(
        rule_predicate_cols - set(re.findall(r"\br\.([a-zA-Z_][a-zA-Z0-9_]*)\b", naive_on_clause))
    )
    unconsumed_guarded = sorted(
        rule_predicate_cols
        - set(re.findall(r"\br\.([a-zA-Z_][a-zA-Z0-9_]*)\b", guarded_on_clause))
    )

    naive_rows, naive_distinct_tx, naive_alpha_bps, naive_alpha_fee_eur = cur.execute(
        f"""
        SELECT
            COUNT(*),
            COUNT(DISTINCT p.tx_id),
            AVG(CASE WHEN p.merchant = 'M_Alpha' THEN r.rate_bps END),
            SUM(CASE WHEN p.merchant = 'M_Alpha' THEN p.eur_amount * r.rate_bps / 10000.0 END)
        FROM payments p
        JOIN fee_rules r ON {naive_on_clause}
        """
    ).fetchone()

    guarded_rows, guarded_distinct_tx, true_alpha_bps, true_alpha_fee_eur = cur.execute(
        f"""
        WITH merchant_monthly AS (
            SELECT
                merchant,
                CASE WHEN SUM(eur_amount) >= 1000.0 THEN 'HIGH_VOL' ELSE 'LOW_VOL' END AS vol_tier,
                CASE WHEN (SUM(CASE WHEN is_fraud = 1 THEN eur_amount ELSE 0.0 END) / SUM(eur_amount)) >= 0.08
                     THEN 'HIGH_FRAUD' ELSE 'LOW_FRAUD' END AS fraud_tier
            FROM payments
            GROUP BY merchant
        )
        SELECT
            COUNT(*),
            COUNT(DISTINCT p.tx_id),
            AVG(CASE WHEN p.merchant = 'M_Alpha' THEN r.rate_bps END),
            SUM(CASE WHEN p.merchant = 'M_Alpha' THEN p.eur_amount * r.rate_bps / 10000.0 END)
        FROM payments p
        JOIN merchant_monthly m ON p.merchant = m.merchant
        JOIN fee_rules r ON {guarded_on_clause}
        """
    ).fetchone()
    conn.close()

    naive_rules_per_tx = naive_rows / naive_distinct_tx
    guarded_rules_per_tx = guarded_rows / guarded_distinct_tx
    bps_rel_err_pct = 100.0 * (naive_alpha_bps - true_alpha_bps) / true_alpha_bps
    fee_sum_inflation_x = naive_alpha_fee_eur / true_alpha_fee_eur

    assert unconsumed_naive == ["fraud_tier", "vol_tier"] and unconsumed_guarded == []
    assert math.isclose(naive_rules_per_tx, 4.0)
    assert math.isclose(guarded_rules_per_tx, 1.0)
    assert math.isclose(naive_alpha_bps, 215.0) and math.isclose(true_alpha_bps, 110.0)
    assert math.isclose(round(bps_rel_err_pct, 2), 95.45)
    assert math.isclose(round(fee_sum_inflation_x, 4), round(4.0 * 215.0 / 110.0, 4))

    # Probe 5b. [exact reproduction of pinned SQL/evaluator logic]
    # Exact reproduction of Future-House/BixBench@49311180bdacb324c596f2e07596c126f2004008
    # bixbench/graders.py:65-108 (_grade_str_verifier, called with partial_match=True in root
    # grade_outputs.py:70-80) and bixbench/graders.py:155-170 (_grade_range_verifier, called by
    # MCQGrader.grade at L201-204), including live upstream false positive `bix-53-q4` in
    # `bixbench-v1.5_results/zero_shot_baselines/gpt-4o-grader-openended.csv` ("5" vs "4.25E-04").
    def bixbench_grade_str_verifier(
        target: str, predicted: str, unsure: str | None = None, partial_match: bool = False
    ) -> dict:
        cleaned_target = re.sub(r"[^a-zA-Z0-9]", "", target).lower()
        cleaned_predicted = re.sub(r"[^a-zA-Z0-9]", "", predicted).lower()
        correct = cleaned_predicted == cleaned_target
        refusal = predicted == unsure if unsure else False
        if not correct and partial_match:
            correct = cleaned_predicted in cleaned_target
        if correct:
            grade_type = "correct"
        elif refusal:
            grade_type = "refused"
        else:
            grade_type = "incorrect"
        return {"grade": 1 if grade_type == "correct" else 0, "grade_type": grade_type}

    def bixbench_grade_range_verifier(target: str, predicted: str) -> dict:
        lower, upper = ast.literal_eval(target)
        correct = lower <= float(predicted) <= upper
        if correct:
            grade_type = "correct"
        return {"grade": 1 if grade_type == "correct" else 0, "grade_type": grade_type}

    num_token_re = re.compile(
        r"(?<![A-Za-z0-9_.+-])[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?(?![A-Za-z0-9_.])"
    )

    def parse_strict_float(s: str) -> float | None:
        txt = s.strip()
        if not txt:
            return None
        try:
            v = float(txt)
        except ValueError:
            return None
        return v if math.isfinite(v) else None

    def hardened_grade_str_verifier(
        target: str, predicted: str, unsure: str | None = None, partial_match: bool = False
    ) -> dict:
        refusal_tokens = {
            "", "na", "n/a", "none", "null", "unsure", "unknown", "insufficientinformation"
        }
        raw_norm = predicted.strip().lower()
        if (unsure and predicted == unsure) or raw_norm in refusal_tokens:
            return {"grade": 0, "grade_type": "refused"}

        # 1. Numeric / signed / scientific-notation targets: preserve sign and exponent!
        t_num = parse_strict_float(target)
        if t_num is not None:
            p_num = parse_strict_float(predicted)
            if p_num is None and partial_match:
                found = num_token_re.findall(predicted)
                if len(found) == 1:
                    p_num = parse_strict_float(found[0])
            if p_num is None:
                return {"grade": 0, "grade_type": "incorrect"}
            ok = math.isclose(p_num, t_num, rel_tol=1e-6, abs_tol=1e-12)
            return {"grade": 1 if ok else 0, "grade_type": "correct" if ok else "incorrect"}

        # 2. Symbolic / text targets: whole-token boundary matching (never raw substring slicing).
        t_tokens = tuple(re.findall(r"[a-z0-9]+", target.lower()))
        p_tokens = tuple(re.findall(r"[a-z0-9]+", predicted.lower()))
        if not p_tokens or "".join(p_tokens) in refusal_tokens:
            return {"grade": 0, "grade_type": "incorrect"}
        correct = p_tokens == t_tokens
        if not correct and partial_match:
            t_len = sum(len(tok) for tok in t_tokens)
            p_len = sum(len(tok) for tok in p_tokens)
            if t_len >= 3 and p_len >= 3:
                if len(t_tokens) <= len(p_tokens):
                    correct = any(
                        p_tokens[i : i + len(t_tokens)] == t_tokens
                        for i in range(len(p_tokens) - len(t_tokens) + 1)
                    )
                else:
                    correct = any(
                        t_tokens[i : i + len(p_tokens)] == p_tokens
                        for i in range(len(t_tokens) - len(p_tokens) + 1)
                    )
        return {"grade": 1 if correct else 0, "grade_type": "correct" if correct else "incorrect"}

    punct_res = bixbench_grade_str_verifier("TP53", "???", partial_match=True)
    na_res = bixbench_grade_str_verifier("mRNA splicing", "N/A", partial_match=True)
    live_bix53_q4_res = bixbench_grade_str_verifier("4.25E-04", "5", partial_match=True)

    hardened_punct = hardened_grade_str_verifier("TP53", "???", partial_match=True)
    hardened_na = hardened_grade_str_verifier("mRNA splicing", "N/A", partial_match=True)
    hardened_bix53_q4 = hardened_grade_str_verifier("4.25E-04", "5", partial_match=True)
    hardened_sign_flip = hardened_grade_str_verifier("-0.85", "+0.85", partial_match=True)
    hardened_exp_flip = hardened_grade_str_verifier("4.25E-04", "4.25E+04", partial_match=True)
    hardened_er_in_determine = hardened_grade_str_verifier(
        "ER", "I cannot determine the answer from the data", partial_match=True
    )
    hardened_5_in_500 = hardened_grade_str_verifier(
        "5", "I found 500 differentially expressed genes", partial_match=True
    )
    hardened_gene_prefix = hardened_grade_str_verifier("TP53", "TP53BP1", partial_match=True)

    hardened_valid_gene = hardened_grade_str_verifier(
        "TP53", "The mutated gene is TP53", partial_match=True
    )
    hardened_valid_sci = hardened_grade_str_verifier("4.25E-04", "4.25e-4", partial_match=True)
    hardened_valid_er = hardened_grade_str_verifier("ER", "er", partial_match=True)

    in_range_ok = bixbench_grade_range_verifier("(0.1, 0.2)", "0.15")
    out_of_range_unbound = False
    try:
        bixbench_grade_range_verifier("(0.1, 0.2)", "0.5")
    except UnboundLocalError:
        out_of_range_unbound = True

    assert punct_res["grade"] == 1 and na_res["grade"] == 1 and live_bix53_q4_res["grade"] == 1
    assert (
        hardened_punct["grade"] == 0
        and hardened_na["grade"] == 0
        and hardened_bix53_q4["grade"] == 0
        and hardened_sign_flip["grade"] == 0
        and hardened_exp_flip["grade"] == 0
        and hardened_er_in_determine["grade"] == 0
        and hardened_5_in_500["grade"] == 0
        and hardened_gene_prefix["grade"] == 0
    )
    assert (
        hardened_valid_gene["grade"] == 1
        and hardened_valid_sci["grade"] == 1
        and hardened_valid_er["grade"] == 1
    )
    assert in_range_ok["grade"] == 1 and out_of_range_unbound is True

    return {
        "dabstep_sqlite_fee_join": {
            "unconsumed_rule_cols_naive": unconsumed_naive,
            "unconsumed_rule_cols_guarded": unconsumed_guarded,
            "naive_rules_matched_per_tx": naive_rules_per_tx,
            "guarded_rules_matched_per_tx": guarded_rules_per_tx,
            "naive_alpha_avg_bps": naive_alpha_bps,
            "true_alpha_avg_bps": true_alpha_bps,
            "bps_relative_inflation_pct": round(bps_rel_err_pct, 2),
            "fee_eur_sum_inflation_factor": round(fee_sum_inflation_x, 4),
        },
        "bixbench_graders_repro": {
            "upstream_question_marks_vs_TP53_grade": punct_res["grade"],
            "upstream_NA_vs_mRNA_splicing_grade": na_res["grade"],
            "upstream_live_bix53_q4_5_vs_4p25em04_grade": live_bix53_q4_res["grade"],
            "hardened_question_marks_grade": hardened_punct["grade"],
            "hardened_NA_grade_type": hardened_na["grade_type"],
            "hardened_bix53_q4_5_vs_4p25em04_grade": hardened_bix53_q4["grade"],
            "hardened_sign_flip_neg0p85_vs_pos0p85_grade": hardened_sign_flip["grade"],
            "hardened_exp_flip_em04_vs_ep04_grade": hardened_exp_flip["grade"],
            "hardened_ER_vs_determine_sentence_grade": hardened_er_in_determine["grade"],
            "hardened_5_vs_500_sentence_grade": hardened_5_in_500["grade"],
            "hardened_TP53_vs_TP53BP1_grade": hardened_gene_prefix["grade"],
            "hardened_valid_TP53_sentence_grade": hardened_valid_gene["grade"],
            "hardened_valid_4p25em4_grade": hardened_valid_sci["grade"],
            "range_verifier_in_range_grade": in_range_ok["grade"],
            "range_verifier_out_of_range_raises_UnboundLocalError": out_of_range_unbound,
        },
    }


def main() -> None:
    p1 = run_probe_p1()
    p2 = run_probe_p2()
    p3 = run_probe_p3()
    p4 = run_probe_p4()
    p5 = run_probe_p5()

    results = {
        "Probe_1": p1,
        "Probe_2": p2,
        "Probe_3": p3,
        "Probe_4": p4,
        "Probe_5": p5,
    }
    canonical = json.dumps(results, sort_keys=True, separators=(",", ":"))
    digest = hashlib.sha256(canonical.encode("utf-8")).hexdigest()

    g3 = p3["grouped_tabular_tree_search"]
    mv60 = p4["multiverse_48branch_ablation"]["rho_0p60"]
    mv85 = p4["multiverse_48branch_ablation"]["rho_0p85"]

    lines = [
        "==============================================================================",
        "Data Analysis, Enterprise SQL, ML Engineering & Scientific Discovery Probes",
        "==============================================================================",
        f"Probe 1a {B_EXACT_CODE}",
        f"  ETM Rule 25 (treeMatch.py:1738-1803) SQLite3: LEFT JOIN FK={p1['etm_rule25_sqlite']['left_join_fk_is_null']}, "
        f"LEFT JOIN non-key={p1['etm_rule25_sqlite']['left_join_nullable_nonkey_is_null']} vs NOT IN={p1['etm_rule25_sqlite']['etm_rule25_not_in_rewrite']}",
        f"Probe 1b {B_CONTROLLED}",
        f"  SQLite3 1:N x 1:M chasm-trap: true={p1['chasm_trap_sqlite']['true_invoice_sum']} vs "
        f"naive_join={p1['chasm_trap_sqlite']['naive_multi_join_sum']} ({p1['chasm_trap_sqlite']['grain_fanout_ratio']}x) vs "
        f"CTE_guarded={p1['chasm_trap_sqlite']['cte_pre_aggregated_sum']}",
        f"Probe 1c {B_EXACT_CODE}",
        f"  Spider2 evaluate.py:84-131 (lite=547/547, snow=547/547, dbt=68/68 ignore_order(s)): "
        f"corrupted_spider2={p1['spider2_evaluate_sqlite']['corrupted_sql_spider2_score']} vs "
        f"sound={p1['spider2_evaluate_sqlite']['corrupted_sql_sound_score']} "
        f"(reordered_nc={p1['spider2_evaluate_sqlite']['reordered_valid_sql_sound_score']}, "
        f"exp_0.999999_vs_1.000001_nc={p1['spider2_evaluate_sqlite']['exp_boundary_0p999999_vs_1p000001_sound_score']})",
        f"Probe 1d {B_ANALYTICAL} + {B_CONTROLLED}",
        f"  CHASE-SQL Alg. 3 (K=21, m=14, p=0.7101): ordered(i!=j,238c) E[r_c]={p1['chase_sql_alg3']['exp_score_wrong_member_ordered_i_ne_j']} < "
        f"E[r_c*]={p1['chase_sql_alg3']['exp_score_singleton_correct_ordered_i_ne_j']} (win={p1['chase_sql_alg3']['ordered_alg3_238calls_win_rate']}, "
        f"Copeland clone flip: {p1['chase_sql_alg3']['ordered_copeland_dedup_winner']}->{p1['chase_sql_alg3']['ordered_copeland_cloned_B_winner']}, "
        f"dedup_BT_cloned={p1['chase_sql_alg3']['cloned_B_dedup_bradley_terry_winner']}); "
        f"unordered(i<j,119c) m*_flash={p1['chase_sql_alg3']['critical_m_unordered_flash_p07101']} "
        f"(asym_win={p1['chase_sql_alg3']['unordered_asym_119calls_win_rate']}, sym_nc={p1['chase_sql_alg3']['unordered_sym_nc_119calls_win_rate']}); "
        f"dedup_1v(28c)={p1['chase_sql_alg3']['cluster_dedup_1vote_28calls_win_rate']}, "
        f"dedup_3v(84c)={p1['chase_sql_alg3']['cluster_dedup_3vote_84calls_win_rate']}, "
        f"dedup_7v_BT(196c)={p1['chase_sql_alg3']['cluster_dedup_7vote_bradley_terry_196calls_win_rate']}",
        f"Probe 2  {B_EXACT_CODE}",
        f"  CHESS preprocess.py:40,87-90 + SequenceMatcher (top_n=10): dropped_cols={len(p2['dropped_business_columns'])}, "
        f"uniform_62_short_recall={p2['uniform_62_short_code_recall_chess']}->{p2['uniform_62_short_code_recall_fixed']}, "
        f"dropped_col_recall={p2['substring_dropped_col_recall_chess']}->{p2['substring_dropped_col_recall_fixed']} "
        f"(id_cols_nc={p2['fixed_false_indexed_id_cols_nc']})",
        f"Probe 3a {B_EXACT_CODE}",
        f"  AIDE journal.py:162-228 _metric_rank conflict: min_rmse_picked={p3['aide_journal_direction_bug']['minimize_rmse_selected_node']}, "
        f"max_auc_picked={p3['aide_journal_direction_bug']['maximize_auc_selected_node']} (warnings={p3['aide_journal_direction_bug']['logged_warnings_without_rejection']})",
        f"Probe 3b {B_CONTROLLED}",
        f"  De-confounded grouped Ridge search (matched 192-row fit): "
        f"raw_192refit(clean={g3['clean_raw_aide_192refit']['test_r2']}, leak={g3['leak_raw_aide_192refit']['test_r2']}, hijack={g3['leak_raw_aide_192refit']['z_ent_select_rate']}) | "
        f"pure_GroupKFold(clean={g3['clean_pure_greedy_group_oof_192fit']['test_r2']}, leak={g3['leak_pure_greedy_group_oof_192fit']['test_r2']}, fwl_sel={g3['leak_pure_greedy_group_oof_192fit']['z_ent_select_rate']}) | "
        f"full_guarded(clean={g3['clean_full_guarded_group_oof_192fit']['test_r2']}, leak={g3['leak_full_guarded_group_oof_192fit']['test_r2']}, hijack={g3['leak_full_guarded_group_oof_192fit']['z_ent_select_rate']}, gap={g3['leak_full_guarded_group_oof_192fit']['report_gap']})",
        f"Probe 4a {B_EXACT_CODE} + {B_ANALYTICAL}",
        f"  DiscoveryBench new_eval.py:418-432: paper_hms={p4['discoverybench_new_eval_bugs']['half_context_match_n4_m4_M2']['paper_hms']} vs "
        f"deployed={p4['discoverybench_new_eval_bugs']['half_context_match_n4_m4_M2']['deployed_score']} (nc={p4['discoverybench_new_eval_bugs']['full_context_match_negative_control']['deployed_score']}); "
        f"unseg_var_leak={p4['discoverybench_new_eval_bugs']['unsegmented_hypo_var_leak_score']} vs seg={p4['discoverybench_new_eval_bugs']['segmented_subhypo_clean_score']}",
        f"Probe 4b {B_CONTROLLED}",
        f"  Multiverse M=48 Lockbox spec-curve confirmation: "
        f"rho=0.60 collider(no_sc={mv60['null_single_spec_collider_h0']['split_bh_lockbox_no_speccurve']} -> 1spec_lb={mv60['null_single_spec_collider_h0']['single_spec_lockbox']} -> curve_lb={mv60['null_single_spec_collider_h0']['full_speccurve_lockbox']}, H1={mv60['alt_true_signal_h1']['full_speccurve_lockbox']}); "
        f"rho=0.85 collider(1spec_lb={mv85['null_single_spec_collider_h0']['single_spec_lockbox']} -> curve_lb={mv85['null_single_spec_collider_h0']['full_speccurve_lockbox']}, H1={mv85['alt_true_signal_h1']['full_speccurve_lockbox']})",
        f"Probe 5a {B_CONTROLLED}",
        f"  DABstep SQLite3 fee join (unconsumed={p5['dabstep_sqlite_fee_join']['unconsumed_rule_cols_naive']}): "
        f"naive_rules/tx={p5['dabstep_sqlite_fee_join']['naive_rules_matched_per_tx']} "
        f"({p5['dabstep_sqlite_fee_join']['naive_alpha_avg_bps']} vs {p5['dabstep_sqlite_fee_join']['true_alpha_avg_bps']} bps, "
        f"+{p5['dabstep_sqlite_fee_join']['bps_relative_inflation_pct']}% rate / {p5['dabstep_sqlite_fee_join']['fee_eur_sum_inflation_factor']}x EUR sum)",
        f"Probe 5b {B_EXACT_CODE}",
        f"  BixBench graders.py:65-108,155-170 & grade_outputs.py:70-80: "
        f"upstream('???'={p5['bixbench_graders_repro']['upstream_question_marks_vs_TP53_grade']}, "
        f"'N/A'={p5['bixbench_graders_repro']['upstream_NA_vs_mRNA_splicing_grade']}, "
        f"bix-53-q4='5'_vs_'4.25E-04'={p5['bixbench_graders_repro']['upstream_live_bix53_q4_5_vs_4p25em04_grade']}) -> "
        f"hardened(all_8_adversarial=0, valid=1); out_of_range_UnboundLocalError={p5['bixbench_graders_repro']['range_verifier_out_of_range_raises_UnboundLocalError']}",
        "------------------------------------------------------------------------------",
        json.dumps({"sha256_12": digest[:12], "sha256": digest, "results": results}, indent=2),
    ]
    print("\n".join(lines))


if __name__ == "__main__":
    main()
