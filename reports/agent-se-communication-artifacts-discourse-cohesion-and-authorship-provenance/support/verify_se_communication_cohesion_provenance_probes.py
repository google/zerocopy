#!/usr/bin/env python3
"""Standalone Python 3.10+ standard-library verification suite for software
engineering communication artifacts, reader-grounded discourse cohesion, and
AI-authorship provenance.

Zero non-stdlib imports, zero disk writes, zero network calls, deterministic
output across PYTHONHASHSEED values.

Probes:
  1.  Flesch-Kincaid Grade Level (stdlib regex syllable heuristic) vs.
      Britton-Gulgoz / Kintsch argument-overlap cohesion, Gopen-Swan
      Given-in-Topic anchoring, and Davison-Kantor causal-connective density
      over multi-sentence technical prose triples (chopped, New-before-Given
      inverted, and principled; every passage satisfies n_sents >= 2).
  2A. Steidl et al. (ICPC 2013) separated Sec. VI.A member-comment coherence
      coefficient (c_coeff, Figs. 2-4) and Sec. VI.B inline-comment word-count
      criterion (Fig. 5), plus counterfactual tests showing why misapplying
      member-level c_coeff to inline comments yields unstable scores and false
      alarms on AST-unrecoverable invariants.
  2B. Tian et al. (ICSE 2022, WhatMakesAGoodCM@2f7c1e33) exact 1,649 / 1,597
      atomic-commit label distribution and verbatim-regex Why-marker audit
      (optional live CSV verification via --tian-csv <path>).
  2C. Minimal lexical-stem mechanism illustration of diff-only vs.
      issue-grounded commit Why verification, including explicit paraphrase
      false-positive and bare-issue-link boundary cases.
  3A. Exact port of coinse/libro@645473db selection, output-cluster ranking,
      and cross-cluster round-robin interleaving on Defects4J (570 FIB bugs)
      and GHRB (25 FIB bugs), with order-invariance and real rescue checks.
  3B. Parametric synthetic stress harness (200 bugs, 50 samples/bug)
      subordinated to Probe 3A's real Defects4J/GHRB replay.
  3C. Derived arithmetic verification of Yu et al. (2026, arXiv:2606.22711v1)
      Tables 1-3 across 33,596 AIDev AI-agent PRs (human Co-Authored-By
      Simpson's paradox, Yates vs. Pearson chi-square, and persistent
      author/committer collaboration-mode gradient).
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import csv
import hashlib
import json
import math
from pathlib import Path
import random
import re
from typing import Sequence


# ============================================================================
# PROBE 1: Flesch-Kincaid vs. Kintsch / Britton-Gulgoz / Gopen-Swan Cohesion
#          & Davison-Kantor Connective Density (All Variants n_sents >= 2)
# ============================================================================

STOPWORDS: frozenset[str] = frozenset({
    "a", "an", "and", "are", "as", "at", "be", "been", "being", "by", "can",
    "could", "did", "do", "does", "for", "from", "had", "has", "have", "in",
    "into", "is", "it", "its", "may", "might", "must", "no", "not", "of",
    "on", "or", "our", "should", "such", "than", "that", "the", "their",
    "them", "then", "there", "these", "they", "this", "those", "to", "was",
    "we", "were", "what", "when", "which", "who", "will", "with", "would",
})

CAUSAL_CONTRASTIVE_CONNECTIVES: frozenset[str] = frozenset({
    "because", "therefore", "consequently", "although", "though", "whereas",
    "unless", "otherwise", "hence", "thus", "since",
})


def count_syllables(word: str) -> int:
    """Stdlib regex syllable approximation for Flesch-Kincaid Grade Level.

    Individual multi-vowel English words (for example, 'timeout', 'balances',
    'acquire') can differ by +/-1 syllable relative to dictionary hyphenation,
    while the multi-grade directional FKGL gap between connective-stripped
    chopped prose and cohesive technical prose remains invariant.
    """
    w = re.sub(r"[^a-z]", "", word.lower())
    if not w:
        return 0
    if len(w) <= 3:
        return 1
    w = re.sub(r"(?:[^laeiouy]es|ed|[^laeiouy]e)$", "", w)
    w = re.sub(r"^y", "", w)
    groups = re.findall(r"[aeiouy]{1,2}", w)
    return max(1, len(groups))


def stem_lite(word: str) -> str:
    w = re.sub(r"[^a-z0-9_]", "", word.lower())
    for suf in (
        "ations", "ation", "ments", "ment", "ings", "ing",
        "edly", "ed", "ers", "er", "ies", "es", "s",
    ):
        if len(w) > len(suf) + 3 and w.endswith(suf):
            if suf == "ies":
                return w[:-3] + "y"
            return w[:-len(suf)]
    return w


def count_overlap_components(content_sets: Sequence[frozenset[str]]) -> int:
    """Connected components in the undirected sentence argument-overlap graph."""
    n = len(content_sets)
    if n == 0:
        return 0
    parent = list(range(n))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a: int, b: int) -> None:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    for i in range(n):
        for j in range(i + 1, n):
            if content_sets[i] & content_sets[j]:
                union(i, j)
    return len({find(i) for i in range(n)})


def analyze_discourse_cohesion(text: str) -> dict[str, float | int | None]:
    """Compute surface FKGL/FRE alongside inter-sentence cohesion metrics.

    Inter-sentence ratios (adj_arg_overlap, given_in_topic, graph_connectivity)
    return None when n_sents < 2 rather than masking undefined 0/0 divisions.
    """
    sentences = [s.strip() for s in re.split(r"(?<=[.!?])\s+", text.strip()) if s.strip()]
    words_per_sent = [re.findall(r"[A-Za-z0-9_'-]+", s) for s in sentences]
    all_words = [w for ws in words_per_sent for w in ws]
    n_sents = len(sentences)
    n_words = len(all_words)
    n_syll = sum(count_syllables(w) for w in all_words)

    fk_grade = 0.39 * (n_words / n_sents) + 11.8 * (n_syll / n_words) - 15.59
    flesch_ease = 206.835 - 1.015 * (n_words / n_sents) - 84.6 * (n_syll / n_words)

    content_sets: list[frozenset[str]] = []
    topic_sets: list[frozenset[str]] = []
    connective_count = 0

    for ws in words_per_sent:
        low = [w.lower().strip("'-") for w in ws]
        connective_count += sum(1 for w in low if w in CAUSAL_CONTRASTIVE_CONNECTIVES)
        joined = " ".join(low)
        connective_count += len(re.findall(r"\b(?:so that|in order to|as a result)\b", joined))
        c_stems = frozenset(
            stem_lite(w) for w in low
            if w not in STOPWORDS and w not in CAUSAL_CONTRASTIVE_CONNECTIVES and len(w) > 2
        )
        content_sets.append(c_stems)
        k_topic = max(3, math.ceil(0.35 * len(low)))
        t_stems = frozenset(
            stem_lite(w) for w in low[:k_topic]
            if w not in STOPWORDS and w not in CAUSAL_CONTRASTIVE_CONNECTIVES and len(w) > 2
        )
        topic_sets.append(t_stems)

    if n_sents < 2:
        adj_arg_overlap: float | None = None
        given_in_topic: float | None = None
        graph_connectivity: float | None = None
    else:
        adj_overlaps = 0
        given_topic_hits = 0
        prior_stems: set[str] = set(content_sets[0])
        for i in range(1, n_sents):
            if content_sets[i - 1] & content_sets[i]:
                adj_overlaps += 1
            if topic_sets[i] & prior_stems:
                given_topic_hits += 1
            prior_stems |= set(content_sets[i])
        n_transitions = n_sents - 1
        n_components = count_overlap_components(content_sets)
        adj_arg_overlap = round(adj_overlaps / n_transitions, 3)
        given_in_topic = round(given_topic_hits / n_transitions, 3)
        graph_connectivity = round((n_sents - n_components) / n_transitions, 3)

    return {
        "n_sents": n_sents,
        "words_per_sent": round(n_words / n_sents, 2),
        "fk_grade": round(fk_grade, 2),
        "flesch_ease": round(flesch_ease, 2),
        "adj_arg_overlap": adj_arg_overlap,
        "graph_connectivity": graph_connectivity,
        "given_in_topic": given_in_topic,
        "connectives_per_sent": round(connective_count / n_sents, 3),
    }


# Each tuple: (topic, chopped_5sent, inverted_new_before_given_3sent, principled_given_before_new_3sent)
PROSE_PAIRS: tuple[tuple[str, str, str, str], ...] = (
    (
        "lease_fencing",
        (
            "The lease daemon checks term numbers. Network partitions delay heartbeats. "
            "Stale workers issue writes. Data corruption happens. Fencing tokens reject old terms."
        ),
        (
            "Because network partitions delay periodic heartbeats, the lease daemon tracks monotonic terms. "
            "Although stale workers still issue asynchronous storage mutations, expired terms persist after delayed heartbeats. "
            "Silent corruption occurs unless strict validation guards reject those stale mutations."
        ),
        (
            "The lease daemon validates monotonic fencing tokens on every write because network partitions can delay heartbeats. "
            "Delayed heartbeats leave stale workers active, although those stale workers hold expired terms. "
            "Expired terms fail fencing validation; therefore, the storage engine rejects stale writes before corruption occurs."
        ),
    ),
    (
        "cache_invalidation",
        (
            "Clients query replica nodes. Primary records change. Replicas serve old pages. "
            "Users see broken balances. Version stamps expire stale entries."
        ),
        (
            "Because asynchronous replication lags behind primary mutations, replica nodes serve prior pages. "
            "Although concurrent readers inspect stale account balances, mismatched entries arise from those prior pages. "
            "Monotonic version stamps expire outdated entries unless fresh updates clear those stale balances."
        ),
        (
            "Replica nodes attach monotonic version stamps to cached pages because asynchronous replication lags behind primary writes. "
            "Primary writes increment the version stamp, although replicas may temporarily hold prior pages. "
            "Prior pages carry mismatched version stamps; therefore, readers invalidate stale entries unless the versions match."
        ),
    ),
    (
        "retry_idempotency",
        (
            "Gateways time out under load. Callers repeat requests. Ledger writes duplicate charges. "
            "Audits fail. Idempotency keys deduplicate retries."
        ),
        (
            "Because transient gateway timeouts interrupt payment endpoints, client callers repeat network requests. "
            "Although duplicate ledger charges corrupt billing audits, automated retries stem from repeated requests. "
            "Persistent idempotency keys return cached receipts unless novel identifiers bypass duplicate charges."
        ),
        (
            "Payment gateways reject duplicate retries using idempotency keys because network timeouts trigger repeated requests. "
            "Repeated requests reach the ledger service, although the first request may have already committed. "
            "Committed requests persist their idempotency keys; therefore, the ledger returns the cached receipt unless the key is new."
        ),
    ),
    (
        "lock_ordering",
        (
            "Threads acquire shard locks. Workers scan index buckets. Opposite lock orders collide. "
            "Processes hang forever. Canonical lock ranks prevent cycles."
        ),
        (
            "Because concurrent worker threads scan index buckets, arbitrary acquisition sequences collide across shard locks. "
            "Although circular wait cycles freeze stalled processes, opposing orders emerge across those shard locks. "
            "Canonical rank invariants forbid descending edges unless broken guards allow circular cycles."
        ),
        (
            "Worker threads acquire shard mutexes in canonical rank order because opposing lock orders create deadlocks. "
            "Opposing lock orders form circular waits, although each worker holds only a single shard mutex initially. "
            "Canonical rank order forbids descending mutex edges; therefore, circular waits cannot form unless rank invariants break."
        ),
    ),
)


# ============================================================================
# PROBE 2A: Steidl et al. (ICPC 2013) Separated Sec. VI.A Member c_coeff
#           & Sec. VI.B Inline Length + Counterfactual Misapplication Tests
# ============================================================================

def levenshtein(a: str, b: str) -> int:
    if len(a) < len(b):
        a, b = b, a
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        curr = [i]
        for j, cb in enumerate(b, 1):
            cost = 0 if ca == cb else 1
            curr.append(min(curr[-1] + 1, prev[j] + 1, prev[j - 1] + cost))
        prev = curr
    return prev[-1]


def split_identifier(ident: str) -> list[str]:
    """Split acronym-prefixed CamelCase (HTMLEncode), camelCase, and snake_case."""
    s = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1 \2", ident)
    s = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", s)
    parts = s.replace("_", " ").split()
    return [p.lower() for p in parts if p]


INVARIANT_MARKERS: frozenset[str] = frozenset({
    "must", "invariant", "caller", "lock", "mutex", "term", "monotonic",
    "idempotent", "overflow", "saturating", "wraparound", "milliseconds",
    "seconds", "bytes", "degrees", "radians", "tie", "ties", "order",
    "sorted", "non-null", "unsafe", "safety", "precondition", "postcondition",
    "thread-safe", "reentrant", "deadline", "concurrent",
})


def _strip_comment_markup(comment: str) -> list[str]:
    """Strip comment delimiters and Javadoc tag names (@param, @return).

    Note: Following the literal rule in Steidl et al. (ICPC 2013, Sec. VI.A),
    Javadoc tag tokens (@param) are stripped while parameter-name tokens
    (for example, 'str' in Fig. 3 and 'A' in Fig. 4) remain in c_words.
    """
    clean = re.sub(r"(/\*\*?|\*/|//|@[A-Za-z]+)", " ", comment)
    return [w.lower() for w in re.findall(r"[A-Za-z0-9]+", clean)]


def score_steidl_member_comment(comment: str, method_name: str) -> dict[str, object]:
    """Steidl et al. (ICPC 2013, Sec. VI.A) member-comment c_coeff metric.

    Matches a comment word cw to a method subword mw whenever
    levenshtein(cw, mw) < 2. Note the literal 1-character edge case: any
    1-character comment word matches any 1-character identifier subword at
    distance 1 (for example, levenshtein('a', 'x') == 1 < 2); Figs. 2-4 have
    no 1-character method subwords.
    """
    c_words = _strip_comment_markup(comment)
    m_words = split_identifier(method_name)
    if not c_words:
        return {
            "c_coeff": 0.0,
            "matched_words": 0,
            "comment_words": 0,
            "steidl_class": "empty",
        }
    matched = sum(
        1 for cw in c_words
        if any(levenshtein(cw, mw) < 2 for mw in m_words)
    )
    c_coeff = matched / len(c_words)
    if c_coeff == 0.0:
        s_cls = "unrelated_or_poor_ident (c_coeff == 0)"
    elif c_coeff > 0.5:
        s_cls = "trivial_restatement (c_coeff > 0.5)"
    else:
        s_cls = "target_gray_zone (0 < c_coeff <= 0.5)"
    return {
        "c_coeff": round(c_coeff, 3),
        "matched_words": matched,
        "comment_words": len(c_words),
        "steidl_class": s_cls,
    }


def score_steidl_inline_length(comment: str) -> dict[str, object]:
    """Steidl et al. (ICPC 2013, Sec. VI.B) inline-comment word-count criterion."""
    c_words = _strip_comment_markup(comment)
    n_words = len(c_words)
    if n_words == 0:
        cls = "empty_inline"
    elif n_words <= 2:
        cls = "trivial_short_inline (words <= 2)"
    else:
        cls = "substantive_length_inline (words > 2)"
    return {
        "inline_word_count": n_words,
        "inline_length_class": cls,
    }


def test_inline_c_coeff_misapplication(
    comment: str,
    enclosing_method: str,
    body_code: str,
) -> dict[str, object]:
    """Counterfactual test: misapplying member c_coeff to inline comments."""
    member_eval = score_steidl_member_comment(comment, enclosing_method)
    inline_eval = score_steidl_inline_length(comment)
    c_words = _strip_comment_markup(comment)
    body_tokens = {t.lower() for t in re.findall(r"[A-Za-z0-9_]+", body_code)}
    body_subtokens = {sub for tok in body_tokens for sub in split_identifier(tok)} | body_tokens
    non_code_invariants = sorted({
        w for w in c_words
        if w in INVARIANT_MARKERS and not any(levenshtein(w, bt) < 2 for bt in body_subtokens)
    })
    inline_false_alarm = (member_eval["c_coeff"] == 0.0) and (len(non_code_invariants) >= 2)
    return {
        "misapplied_member_c_coeff": member_eval["c_coeff"],
        "inline_word_count": inline_eval["inline_word_count"],
        "inline_length_class": inline_eval["inline_length_class"],
        "invariant_hits": len(non_code_invariants),
        "inline_false_alarm": inline_false_alarm,
    }


# ============================================================================
# PROBE 2B & 2C: Tian et al. (ICSE 2022, WhatMakesAGoodCM@2f7c1e33) Audit
#                & Minimal Lexical-Stem Why-Grounding Mechanism Illustration
# ============================================================================

# Exact 5-repo x 4-class table audited from WhatMakesAGoodCM/What-Makes-a-Good-Commit-Message@2f7c1e33
# File: Dataset/sampled messages.csv (1,649 total rows = 1,597 atomic + 52 multi-change).
# Tuple: (repo_id, project, total_sampled, multi_change, label0_both, label3_no_why, label2_no_what, label1_neither)
TIAN_2022_REPO_COUNTS: tuple[tuple[int, str, int, int, int, int, int, int], ...] = (
    (1, "junit-team/junit4",            323,  3, 135, 122, 39, 24),
    (2, "apache/dubbo",                 328, 25, 170,  61, 59, 13),
    (3, "square/retrofit",              283,  0, 125, 132, 19,  7),
    (4, "square/okhttp",                338, 20, 182,  96, 37,  3),
    (5, "spring-projects/spring-boot",  377,  4, 307,  15, 33, 18),
)

# Exact verbatim regexes directly verified against all 1,597 atomic rows
# (`message` column, `if_mulit_commit != '1'`) of Dataset/sampled messages.csv:
WHY_CLAUSE_REGEX = re.compile(
    r"\b(?:because|since|to\s+(?:prevent|avoid|fix|reduce|ensure|support|allow|mitigate|resolve)|"
    r"so\s+that|in\s+order\s+to|fixes\s+#?\d+|prevent(?:s|ing)?|avoid(?:s|ing)?)\b.*",
    re.IGNORECASE,
)

ISSUE_REF_REGEX = re.compile(r"#\d+|\bgh-\d+\b|https?://", re.IGNORECASE)

# Exact counts produced by WHY_CLAUSE_REGEX, ISSUE_REF_REGEX, and their union
# on all 1,597 atomic commits in Dataset/sampled messages.csv (reproducible via --tian-csv):
# Tuple: (label_code, label_name, n_commits, why_clause_hits, issue_ref_hits, union_hits)
TIAN_2022_MARKER_AUDIT: tuple[tuple[int, str, int, int, int, int], ...] = (
    (0, "Why+What",          919, 99, 551, 591),
    (2, "Why-Only(NoWhat)",  187, 12,  85,  89),
    (3, "What-Only(NoWhy)",  426,  4,  16,  19),
    (1, "Neither",            65,  0,   6,   6),
)


def replay_tian_csv(csv_path: Path) -> dict[str, object]:
    """Optional live replay of WhatMakesAGoodCM@2f7c1e33 Dataset/sampled messages.csv."""
    with csv_path.open("r", encoding="utf-8", errors="replace", newline="") as fh:
        rows = list(csv.DictReader(fh))
    repo_stats: dict[int, list[int]] = {r[0]: [0, 0, 0, 0, 0, 0] for r in TIAN_2022_REPO_COUNTS}
    marker_stats: dict[int, list[int]] = {lbl: [0, 0, 0, 0] for lbl in (0, 2, 3, 1)}
    for row in rows:
        rid = int(row["repo_id"].strip())
        lbl = int(row["label"].strip())
        is_multi = (row.get("if_mulit_commit") or "").strip() == "1"
        repo_stats[rid][0] += 1
        if is_multi:
            repo_stats[rid][1] += 1
            continue
        col_map = {0: 2, 3: 3, 2: 4, 1: 5}
        repo_stats[rid][col_map[lbl]] += 1
        msg = row.get("message") or ""
        w_hit = bool(WHY_CLAUSE_REGEX.search(msg))
        r_hit = bool(ISSUE_REF_REGEX.search(msg))
        marker_stats[lbl][0] += 1
        marker_stats[lbl][1] += int(w_hit)
        marker_stats[lbl][2] += int(r_hit)
        marker_stats[lbl][3] += int(w_hit or r_hit)

    for rid, _, samp, mult, l0, l3, l2, l1 in TIAN_2022_REPO_COUNTS:
        assert tuple(repo_stats[rid]) == (samp, mult, l0, l3, l2, l1), (
            f"Repo {rid} mismatch: {repo_stats[rid]} vs {(samp, mult, l0, l3, l2, l1)}"
        )
    for lbl, _, n_c, w_h, r_h, u_h in TIAN_2022_MARKER_AUDIT:
        assert tuple(marker_stats[lbl]) == (n_c, w_h, r_h, u_h), (
            f"Label {lbl} marker mismatch: {marker_stats[lbl]} vs {(n_c, w_h, r_h, u_h)}"
        )
    return {"rows_verified": len(rows), "exact_match": True}


def audit_commit_why_grounding(diff_text: str, context_text: str, commit_msg: str) -> dict[str, object]:
    """Minimal lexical-stem illustration of diff-only vs. issue-grounded Why checks.

    Demonstrates the conceptual asymmetry (diffs encode What, not unstated Why),
    NOT a production hallucination detector: valid semantic paraphrases lacking
    surface stem overlap trigger false positives, and bare issue links without
    an explicit causal clause return has_why=False under WHY_CLAUSE_REGEX alone.
    """
    diff_stems = {
        stem_lite(t) for t in re.findall(r"[A-Za-z0-9_]+", diff_text)
        if t.lower() not in STOPWORDS and len(t) > 2
    }
    ctx_stems = {
        stem_lite(t) for t in re.findall(r"[A-Za-z0-9_]+", context_text)
        if t.lower() not in STOPWORDS and len(t) > 2
    }

    clauses = [c.strip() for c in re.split(r"[.;\n]+", commit_msg) if c.strip()]
    what_stems: set[str] = set()
    why_stems: set[str] = set()
    for cl in clauses:
        m = WHY_CLAUSE_REGEX.search(cl)
        if m:
            what_part = cl[:m.start()]
            why_part = m.group(0)
        else:
            what_part = cl
            why_part = ""
        for t in re.findall(r"[A-Za-z0-9_]+", what_part):
            if t.lower() not in STOPWORDS and len(t) > 2:
                what_stems.add(stem_lite(t))
        for t in re.findall(r"[A-Za-z0-9_]+", why_part):
            tl = t.lower()
            if (
                tl not in STOPWORDS
                and tl not in {"prevent", "avoid", "fix", "ensure", "reduce", "allow", "order"}
                and len(t) > 2
            ):
                why_stems.add(stem_lite(t))

    what_in_diff = len(what_stems & diff_stems) / max(1, len(what_stems))
    why_in_diff = len(why_stems & diff_stems) / max(1, len(why_stems)) if why_stems else 0.0
    why_in_union = len(why_stems & (diff_stems | ctx_stems)) / max(1, len(why_stems)) if why_stems else 0.0
    return {
        "has_why": bool(why_stems),
        "has_issue_ref": bool(ISSUE_REF_REGEX.search(commit_msg)),
        "what_diff_support": round(what_in_diff, 3),
        "why_diff_only_support": round(why_in_diff, 3),
        "why_context_grounded_support": round(why_in_union, 3),
        "unverified_why_hallucination": bool(why_stems) and why_in_union < 0.4,
    }


# ============================================================================
# PROBE 3A & 3B: LIBRO (coinse/libro@645473db) Exact Selection, Ranking &
#                Round-Robin Replay (Defects4J + GHRB + Stress Harness)
# ============================================================================

# Exact Defects4J frequency distribution from coinse/libro@645473db results/ranking_features_d4j.csv
# Tuple: (max_clus_size_output_fib, n_fib_bugs, n_reproduced_bugs); sum = 570 FIB bugs, 251 reproduced.
LIBRO_D4J_MAX_CLUSTER_FREQ: tuple[tuple[int, int, int], ...] = (
    (1, 220, 32), (2, 77, 24), (3, 36, 15), (4, 28, 17), (5, 23, 16), (6, 20, 14),
    (7, 7, 6), (8, 16, 13), (9, 8, 6), (10, 10, 3), (11, 9, 8), (12, 4, 2),
    (13, 9, 8), (14, 3, 2), (15, 3, 3), (16, 5, 5), (17, 3, 1), (18, 4, 3),
    (19, 3, 2), (20, 4, 3), (21, 4, 4), (22, 3, 3), (23, 1, 1), (24, 1, 1),
    (25, 3, 2), (27, 1, 1), (28, 2, 1), (29, 3, 2), (30, 3, 2), (31, 3, 3),
    (32, 3, 3), (33, 3, 3), (34, 3, 1), (35, 2, 2), (36, 4, 4), (37, 3, 3),
    (38, 2, 2), (39, 8, 8), (40, 2, 2), (41, 5, 4), (42, 5, 4), (43, 1, 1),
    (44, 3, 3), (45, 3, 3), (46, 3, 2), (47, 3, 2), (50, 1, 1),
)

# Exact 25-bug GHRB output-cluster dataset from coinse/libro@645473db
# (results/example2_n50_GHRB.json + results/ranking_features_ghrb.csv).
# Entry: (bug_id, tuple of (clus_size_output_fib, bug_report_match, tuple of (test_length, test_exc_match, success)))
LIBRO_GHRB_CLUSTERS: tuple[tuple[str, tuple[tuple[int, int, tuple[tuple[int, int, int], ...]], ...]], ...] = (
    ("FasterXML_jackson-databind-3195", ((2, 0, ((122, 0, 0), (130, 0, 0))),)),
    ("Hakky54_sslcontext-kickstart-167", ((10, 0, ((41, 0, 0), (59, 0, 0), (39, 0, 0), (50, 0, 0), (57, 0, 0), (46, 0, 0), (39, 0, 0))),)),
    ("Hakky54_sslcontext-kickstart-197", ((1, 0, ((91, 0, 0),)), (1, 0, ((109, 0, 1),)))),
    ("assertj_assertj-core-2324", ((5, 0, ((38, 0, 1), (38, 0, 1), (38, 0, 1), (50, 0, 0), (39, 0, 1))),)),
    ("assertj_assertj-core-2445", ((11, 0, ((117, 0, 0), (95, 0, 1), (40, 0, 0), (48, 0, 0), (72, 0, 0), (68, 0, 0), (56, 0, 0), (79, 0, 0), (39, 0, 0), (39, 0, 0), (54, 0, 0))),)),
    ("assertj_assertj-core-2685", ((12, 0, ((40, 0, 1), (65, 0, 0), (35, 0, 1), (35, 0, 1), (40, 0, 1), (47, 0, 1), (63, 0, 0), (55, 0, 0), (34, 0, 1), (34, 0, 1), (63, 0, 1), (63, 0, 0))), (3, 0, ((48, 0, 0), (120, 0, 0), (47, 0, 0))))),
    ("checkstyle_checkstyle-10839", ((3, 0, ((43, 0, 0), (52, 0, 0), (52, 0, 0))), (1, 0, ((52, 0, 0),)), (1, 0, ((61, 0, 0),)), (1, 0, ((52, 0, 0),)), (2, 0, ((52, 0, 0), (52, 0, 0))), (1, 0, ((52, 0, 0),)), (2, 0, ((52, 0, 0),)), (1, 0, ((61, 0, 0),)), (1, 0, ((56, 0, 0),)), (2, 0, ((61, 0, 0), (52, 0, 0))), (1, 0, ((52, 0, 0),)))),
    ("checkstyle_checkstyle-10840", ((2, 0, ((68, 0, 0), (68, 0, 0))), (1, 0, ((70, 0, 0),)))),
    ("checkstyle_checkstyle-10958", ((5, 0, ((68, 0, 0), (42, 0, 0), (60, 0, 0), (90, 0, 0), (118, 0, 0))), (1, 0, ((70, 0, 0),)), (1, 0, ((62, 0, 0),)), (1, 1, ((14, 0, 0),)), (1, 1, ((118, 0, 0),)), (1, 1, ((70, 0, 0),)), (1, 1, ((68, 0, 0),)), (1, 1, ((94, 0, 0),)), (1, 1, ((77, 0, 0),)), (1, 1, ((119, 0, 0),)), (1, 1, ((77, 0, 0),)), (1, 1, ((68, 0, 0),)), (1, 1, ((63, 0, 0),)))),
    ("checkstyle_checkstyle-10963", ((5, 0, ((42, 0, 0), (41, 0, 0), (41, 0, 0), (42, 0, 0), (42, 0, 0))), (1, 0, ((48, 0, 0),)), (1, 0, ((52, 0, 0),)), (1, 0, ((50, 0, 0),)), (1, 0, ((50, 0, 0),)), (1, 0, ((56, 0, 0),)), (1, 0, ((48, 0, 0),)), (1, 0, ((56, 0, 0),)), (1, 0, ((48, 0, 0),)), (1, 1, ((59, 0, 0),)), (1, 1, ((56, 0, 0),)), (1, 0, ((49, 0, 0),)), (1, 0, ((58, 0, 0),)))),
    ("checkstyle_checkstyle-10967", ((3, 0, ((51, 0, 0), (60, 0, 0), (45, 0, 0))),)),
    ("checkstyle_checkstyle-11020", ((3, 0, ((42, 0, 0), (41, 0, 0), (63, 0, 0))), (1, 1, ((47, 0, 0),)))),
    ("checkstyle_checkstyle-11085", ((1, 1, ((53, 0, 0),)), (1, 0, ((16, 0, 0),)))),
    ("checkstyle_checkstyle-11270", ((1, 0, ((56, 0, 0),)),)),
    ("checkstyle_checkstyle-11383", ((2, 0, ((45, 0, 0), (44, 0, 0))), (1, 0, ((43, 0, 0),)), (1, 0, ((43, 0, 0),)), (1, 0, ((67, 0, 0),)))),
    ("checkstyle_checkstyle-11468", ((3, 0, ((42, 0, 0), (42, 0, 0), (41, 0, 0))), (1, 0, ((43, 0, 0),)), (1, 0, ((52, 0, 0),)), (2, 0, ((50, 0, 0), (50, 0, 0))), (1, 0, ((63, 0, 0),)))),
    ("checkstyle_checkstyle-11926", ((4, 0, ((42, 0, 0), (42, 0, 0), (50, 0, 0), (41, 0, 0))),)),
    ("google_gson-2060", ((1, 0, ((60, 0, 0),)),)),
    ("google_gson-2061", ((1, 0, ((44, 0, 0),)), (1, 0, ((94, 0, 0),)), (20, 0, ((91, 0, 1), (61, 0, 1), (65, 0, 1), (66, 0, 1), (82, 0, 1), (73, 0, 1), (56, 0, 1), (61, 0, 0), (66, 0, 1), (43, 0, 1), (66, 0, 1), (70, 0, 1), (50, 0, 1), (48, 0, 1), (78, 0, 1), (91, 0, 1), (57, 0, 0), (48, 0, 1), (100, 0, 1))), (1, 0, ((68, 0, 0),)))),
    ("google_gson-2130", ((1, 1, ((65, 0, 1),)), (2, 1, ((81, 0, 1), (74, 0, 1))))),
    ("google_gson-2134", ((28, 0, ((90, 1, 1), (45, 1, 1), (45, 1, 1), (90, 1, 1))), (1, 0, ((37, 1, 1),)), (8, 0, ((38, 1, 1), (43, 1, 1), (43, 1, 1), (35, 1, 1))))),
    ("google_gson-2153", ((1, 0, ((40, 0, 0),)), (14, 0, ((25, 0, 0), (26, 0, 0), (42, 0, 0), (40, 0, 0), (40, 0, 0), (28, 0, 0), (36, 0, 0), (38, 0, 0), (28, 0, 0), (23, 0, 0), (30, 0, 0))), (1, 0, ((41, 0, 0),)), (1, 0, ((50, 0, 0),)), (1, 0, ((51, 0, 0),)))),
    ("google_gson-2158", ((2, 0, ((42, 0, 0), (35, 0, 0))), (1, 0, ((26, 0, 0),)), (1, 0, ((79, 0, 1),)), (9, 0, ((36, 0, 1), (111, 0, 1), (79, 0, 1), (33, 0, 1), (72, 0, 0), (31, 0, 1), (143, 0, 0), (111, 0, 1), (26, 0, 1))), (1, 0, ((26, 0, 0),)), (1, 0, ((140, 0, 0),)))),
    ("jhy_jsoup-1648", ((11, 0, ((60, 0, 0), (60, 0, 0), (62, 0, 0), (56, 0, 0), (58, 0, 0), (58, 0, 0), (58, 0, 0), (58, 0, 0), (60, 0, 0))), (1, 0, ((88, 0, 0),)), (2, 0, ((66, 0, 1), (99, 0, 0))))),
    ("jhy_jsoup-1763", ((12, 0, ((61, 0, 0), (75, 0, 0), (75, 0, 0), (69, 0, 0))), (4, 0, ((75, 0, 0), (75, 0, 0), (75, 0, 0))), (1, 0, ((75, 0, 0),)), (15, 0, ((75, 0, 0), (75, 0, 0), (75, 0, 0), (77, 0, 0), (77, 0, 0), (75, 0, 0))), (1, 0, ((77, 0, 0),)), (1, 0, ((81, 0, 1),)), (1, 0, ((68, 0, 1),)))),
)


def compute_roc_auc_from_freq(freq_table: Sequence[tuple[int, int, int]]) -> float:
    """Exact trapezoidal ROC AUC (Mann-Whitney U with ties) from (score, total, positives)."""
    pos_total = sum(p for _, _, p in freq_table)
    neg_total = sum(n - p for _, n, p in freq_table)
    u = 0.0
    for s1, _, p1 in freq_table:
        if p1 == 0:
            continue
        for s0, n0, p0 in freq_table:
            neg0 = n0 - p0
            if neg0 == 0:
                continue
            if s1 > s0:
                u += p1 * neg0
            elif s1 == s0:
                u += 0.5 * p1 * neg0
    return u / (pos_total * neg_total)


def replay_libro_clusters(
    dataset: Sequence[tuple[str, tuple[tuple[int, int, tuple[tuple[int, int, int], ...]], ...]]],
    agreement_threshold: int = 1,
    interleave_clusters: bool = True,
) -> tuple[dict[str, float], dict[str, int]]:
    """Exact port of coinse/libro@645473db scripts/selection_and_ranking.py:25-31, 106-149, 275-290."""
    big_number = 100000
    selected = 0
    reproduced_selected = 0
    total_repro_pool = 0
    acc_at = {1: 0, 3: 0, 5: 0}
    wasted_at_5 = 0
    ranks_by_bug: dict[str, int] = {}

    for bug_id, clusters in dataset:
        has_brt = any(m[2] == 1 for _, _, members in clusters for m in members)
        if has_brt:
            total_repro_pool += 1
        max_csize = max(csize for csize, _, _ in clusters)
        # select_confident_bugs (L25-31): clus_size_output_fib > threshold
        if max_csize <= agreement_threshold:
            continue

        selected += 1
        if has_brt:
            reproduced_selected += 1

        # Cluster scoring (L134-143): (bug_report_match, len(test_paths), -sum_test_length/len(test_paths))
        scored: list[tuple[tuple[int, int, float], int, list[tuple[int, int, int]]]] = []
        for idx, (csize, brm, members) in enumerate(clusters):
            sum_len = sum(m[0] for m in members)
            ordered = sorted(members, key=lambda m: (-m[1], m[0]))
            scored.append(((brm, csize, -sum_len / csize), idx, ordered))
        scored.sort(key=lambda x: x[0], reverse=True)

        delivered: list[tuple[int, int, int]] = []
        if interleave_clusters:
            # Round-robin across clusters (L144-147)
            max_len = max(len(x[2]) for x in scored)
            for i in range(max_len):
                for _, _, ord_m in scored:
                    if i < len(ord_m):
                        delivered.append(ord_m[i])
        else:
            for _, _, ord_m in scored:
                delivered.extend(ord_m)

        succ_ranks = [i + 1 for i, m in enumerate(delivered) if m[2] == 1]
        first_rank = min(succ_ranks) if succ_ranks else big_number
        ranks_by_bug[bug_id] = first_rank
        for k in (1, 3, 5):
            if first_rank <= k:
                acc_at[k] += 1
        # L54 stores len(sorted_fib_tests) under num_clusters; wasted_effort (L283) caps at min(len(delivered), N)
        cap = min(len(delivered), 5)
        wasted_at_5 += (first_rank - 1) if first_rank <= 5 else cap

    summary = {
        "selected": float(selected),
        "reproduced": float(reproduced_selected),
        "precision": round(reproduced_selected / max(1, selected), 4),
        "pool_recall": round(reproduced_selected / max(1, total_repro_pool), 4),
        "acc@1": float(acc_at[1]),
        "acc@3": float(acc_at[3]),
        "acc@5": float(acc_at[5]),
        "mean_wasted@5": round(wasted_at_5 / max(1, selected), 3),
    }
    return summary, ranks_by_bug


def build_synthetic_libro_dataset(
    seed: int = 42,
    n_bugs: int = 200,
    samples_per_bug: int = 50,
) -> list[tuple[str, tuple[tuple[int, int, tuple[tuple[int, int, int], ...]], ...]]]:
    """Parametric stress harness (subordinated to real Defects4J/GHRB replay)."""
    rng = random.Random(seed)
    dataset: list[tuple[str, tuple[tuple[int, int, tuple[tuple[int, int, int], ...]], ...]]] = []
    for b in range(n_bugs):
        has_brt = (b % 5) in (0, 1)
        matches_br = (b % 3 != 0)
        decoy_dominant = has_brt and (not matches_br)
        clusters_raw: dict[str, list[tuple[int, int, int, int]]] = defaultdict(list)

        for _ in range(samples_per_bug):
            r = rng.random()
            if r < 0.78:
                continue  # compile error or passes on buggy (non-FIB)
            if has_brt and ((not decoy_dominant and rng.random() < 0.55) or (decoy_dominant and rng.random() < 0.28)):
                brm = 1 if matches_br else 0
                tem = 1 if (matches_br and rng.random() < 0.6) else 0
                clusters_raw["true_brt_sig"].append((brm, rng.randint(18, 48), tem, 1))
            else:
                decoy_id = 0 if (decoy_dominant and rng.random() < 0.65) else rng.randint(1, 14)
                clusters_raw[f"spurious_sig_{decoy_id}"].append((0, rng.randint(30, 95), 0, 0))

        if not clusters_raw:
            continue
        clus_list = []
        for sig in sorted(clusters_raw.keys()):
            items = clusters_raw[sig]
            brm = items[0][0]
            members = tuple((tlen, tem, succ) for _, tlen, tem, succ in items)
            clus_list.append((len(items), brm, members))
        dataset.append((f"SYN-{b:03d}", tuple(clus_list)))
    return dataset


# ============================================================================
# PROBE 3C: Yu et al. (2026, arXiv:2606.22711v1) Tables 1-3 Arithmetic Audit
#           All 33,596 AIDev PRs are AI-agent PRs; Co-Authored-By marks a
#           HUMAN co-author (human-agent collaborative vs. pure autonomous).
# ============================================================================

# Table 1 exact integer counts & published merge rates
YU_2026_TABLE1_COAUTH_N = 10764
YU_2026_TABLE1_PURE_N = 22832
YU_2026_TABLE1_COAUTH_MR = 0.538
YU_2026_TABLE1_PURE_MR = 0.798

# Table 2 published per-agent counts, 1-decimal rates, and published deltas (pp)
# Tuple: (agent, n_prs, pct_human_coauth, mr_human_coauth, mr_pure_agent, published_delta_pp)
YU_2026_TABLE2: tuple[tuple[str, int, float, float, float, float], ...] = (
    ("Codex",       21799, 0.012, 0.783, 0.826, -4.4),
    ("Copilot",      4970, 0.894, 0.474, 0.062, 41.2),
    ("Devin",        4827, 0.959, 0.551, 0.216, 33.5),
    ("Cursor",       1541, 0.698, 0.663, 0.627,  3.7),
    ("Claude Code",   459, 0.767, 0.602, 0.551,  5.1),
)

# Table 3 author/committer collaboration modes (n = 33,564; excludes 16 human-author/bot-committer
# and 16 PRs lacking commit metadata)
YU_2026_TABLE3: tuple[tuple[str, int, float], ...] = (
    ("fully_autonomous", 10028, 47.6),
    ("agent_draft",        336, 64.3),
    ("human_both",       23200, 82.0),
)


def verify_yu_2026_tables() -> dict[str, object]:
    total_prs = sum(n for _, n, _, _, _, _ in YU_2026_TABLE2)
    assert total_prs == YU_2026_TABLE1_COAUTH_N + YU_2026_TABLE1_PURE_N == 33596

    # Reconstructed pooled merge rates from Table 2's 1-decimal rounded cells
    n_coauth_rec = sum(n * p for _, n, p, _, _, _ in YU_2026_TABLE2)
    n_pure_rec = sum(n * (1.0 - p) for _, n, p, _, _, _ in YU_2026_TABLE2)
    m_coauth_rec = sum(n * p * mc for _, n, p, mc, _, _ in YU_2026_TABLE2)
    m_pure_rec = sum(n * (1.0 - p) * mp for _, n, p, _, mp, _ in YU_2026_TABLE2)
    pooled_co_rec = m_coauth_rec / n_coauth_rec
    pooled_pu_rec = m_pure_rec / n_pure_rec
    pooled_delta_rec_pp = 100.0 * (pooled_co_rec - pooled_pu_rec)

    # Excluding dominant Codex (64.9% of dataset, 1.2% human co-auth, 82.6% pure-agent MR)
    non_codex = [row for row in YU_2026_TABLE2 if row[0] != "Codex"]
    nc_co = sum(n * p for _, n, p, _, _, _ in non_codex)
    nc_pu = sum(n * (1.0 - p) for _, n, p, _, _, _ in non_codex)
    nc_m_co = sum(n * p * mc for _, n, p, mc, _, _ in non_codex)
    nc_m_pu = sum(n * (1.0 - p) * mp for _, n, p, _, mp, _ in non_codex)
    non_codex_delta_pp = 100.0 * ((nc_m_co / nc_co) - (nc_m_pu / nc_pu))

    published_within = {ag: pub_d for ag, _, _, _, _, pub_d in YU_2026_TABLE2}
    reconstructed_within = {ag: round(100.0 * (mc - mp), 1) for ag, _, _, mc, mp, _ in YU_2026_TABLE2}
    unweighted_pub_mean_pp = sum(published_within.values()) / len(published_within)
    positive_agents = sum(1 for d in published_within.values() if d > 0.0)

    # Table 1 2x2 chi-square check (10,764 human-coauth @ 53.8% vs 22,832 pure-agent @ 79.8%)
    a = round(YU_2026_TABLE1_COAUTH_N * YU_2026_TABLE1_COAUTH_MR)
    b = YU_2026_TABLE1_COAUTH_N - a
    c = round(YU_2026_TABLE1_PURE_N * YU_2026_TABLE1_PURE_MR)
    d = YU_2026_TABLE1_PURE_N - c
    n_tab1 = a + b + c + d
    denom = (a + b) * (c + d) * (a + c) * (b + d)
    chi2_pearson = n_tab1 * (a * d - b * c) ** 2 / denom
    chi2_yates = n_tab1 * (max(0.0, abs(a * d - b * c) - n_tab1 / 2.0)) ** 2 / denom

    # Table 3 collaboration-mode total and strict monotonicity
    tab3_total = sum(n for _, n, _ in YU_2026_TABLE3)
    tab3_rates = [mr for _, _, mr in YU_2026_TABLE3]
    assert tab3_total == 33564 and tab3_rates == sorted(tab3_rates) and len(set(tab3_rates)) == 3

    return {
        "total_prs": total_prs,
        "codex_share_pct": round(100.0 * 21799 / total_prs, 1),
        "table1_n_human_coauth": YU_2026_TABLE1_COAUTH_N,
        "table1_n_pure_agent": YU_2026_TABLE1_PURE_N,
        "reconstructed_n_human_coauth": round(n_coauth_rec, 2),
        "reconstructed_n_pure_agent": round(n_pure_rec, 2),
        "reconstructed_pooled_mr_coauth_pct": round(100.0 * pooled_co_rec, 2),
        "reconstructed_pooled_mr_pure_pct": round(100.0 * pooled_pu_rec, 2),
        "reconstructed_pooled_delta_pp": round(pooled_delta_rec_pp, 2),
        "table1_chi2_yates": round(chi2_yates, 2),
        "table1_chi2_pearson": round(chi2_pearson, 2),
        "positive_within_agent_count": positive_agents,
        "published_within_deltas_pp": published_within,
        "reconstructed_within_deltas_pp": reconstructed_within,
        "unweighted_published_within_mean_pp": round(unweighted_pub_mean_pp, 2),
        "excluding_codex_pooled_delta_pp": round(non_codex_delta_pp, 2),
        "table3_total_prs": tab3_total,
        "table3_modes": {mode: {"n": n, "merge_rate_pct": mr} for mode, n, mr in YU_2026_TABLE3},
    }


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--tian-csv",
        type=Path,
        default=None,
        help="Optional local path to WhatMakesAGoodCM@2f7c1e33 Dataset/sampled messages.csv for live regex/count replay.",
    )
    args = parser.parse_args(argv)

    payload: dict[str, object] = {}

    print("================================================================================")
    print("PROBE 1 [derived analytical / simulation model]:")
    print("  Flesch-Kincaid (Regex Syllable Heuristic) vs. Kintsch/Gopen-Swan/Davison-Kantor")
    print("================================================================================")
    # Confirm 1-sentence edge case returns None rather than masking 0/0 as 0.000
    single_check = analyze_discourse_cohesion("Single sentence without transitions.")
    assert single_check["n_sents"] == 1
    assert single_check["adj_arg_overlap"] is None
    assert single_check["given_in_topic"] is None
    assert single_check["graph_connectivity"] is None

    p1_records: dict[str, object] = {}
    for topic, chopped, inverted, principled in PROSE_PAIRS:
        r_chop = analyze_discourse_cohesion(chopped)
        r_inv = analyze_discourse_cohesion(inverted)
        r_prin = analyze_discourse_cohesion(principled)
        for tag, rec in (("chopped", r_chop), ("inverted", r_inv), ("principled", r_prin)):
            assert int(rec["n_sents"]) >= 2, f"{topic}/{tag} must have >= 2 sentences"
            print(
                f"  [{topic}] {tag:10s} (S={rec['n_sents']}): FKGL={rec['fk_grade']:5.2f} "
                f"FRE={rec['flesch_ease']:5.2f} adj_ovlp={rec['adj_arg_overlap']:.3f} "
                f"conn_graph={rec['graph_connectivity']:.3f} given_topic={rec['given_in_topic']:.3f} "
                f"conn/sent={rec['connectives_per_sent']:.3f}"
            )
        assert float(r_chop["fk_grade"]) < float(r_prin["fk_grade"])
        assert float(r_chop["connectives_per_sent"]) == 0.0 and float(r_prin["connectives_per_sent"]) >= 1.0
        assert float(r_chop["adj_arg_overlap"]) < float(r_prin["adj_arg_overlap"])
        assert float(r_chop["graph_connectivity"]) < float(r_prin["graph_connectivity"])
        assert float(r_inv["connectives_per_sent"]) >= 1.0 and float(r_inv["adj_arg_overlap"]) == 1.0
        assert float(r_inv["given_in_topic"]) == 0.0 and float(r_prin["given_in_topic"]) == 1.0
        p1_records[topic] = {"chopped": r_chop, "inverted": r_inv, "principled": r_prin}
    payload["probe_1"] = p1_records

    print("\n================================================================================")
    print("PROBE 2A [exact calculation on published examples] + [derived counterfactual]:")
    print("  Steidl et al. (ICPC 2013) Sec. VI.A Member c_coeff (Figs. 2-4) & Sec. VI.B Inline Length (Fig. 5)")
    print("================================================================================")
    assert split_identifier("HTMLEncode") == ["html", "encode"]
    assert split_identifier("removeAllMarkers") == ["remove", "all", "markers"]
    assert levenshtein("a", "x") == 1  # Documented 1-char Levenshtein < 2 edge case

    member_cases = [
        ("steidl_fig2_trivial_member", "/** removes all defined markers */", "removeAllMarkers"),
        ("steidl_fig3_unanchored_member", "/** Thanks to benoit.heinrich on forum.java.sun.com \n * @param str \n */", "HTMLEncode"),
        ("steidl_fig4_opaque_ident", "/** Check for symmetry, then construct the eigenvalue decomposition @param A square matrix */", "calc"),
        ("steidl_fig4_renamed_ident", "/** Check for symmetry, then construct the eigenvalue decomposition @param A square matrix */", "calcEigenvalueDecomposition"),
    ]
    p2a_member: dict[str, object] = {}
    for label, cmt, fn in member_cases:
        out = score_steidl_member_comment(cmt, fn)
        p2a_member[label] = out
        print(
            f"  [Sec. VI.A member] {label:29s}: c_coeff={out['c_coeff']:.3f} "
            f"({out['matched_words']}/{out['comment_words']}) | {out['steidl_class']}"
        )
    assert p2a_member["steidl_fig2_trivial_member"]["c_coeff"] == 0.75
    assert p2a_member["steidl_fig3_unanchored_member"]["c_coeff"] == 0.0
    assert p2a_member["steidl_fig4_opaque_ident"]["c_coeff"] == 0.0
    assert 0.0 < float(p2a_member["steidl_fig4_renamed_ident"]["c_coeff"]) <= 0.5

    # Sec. VI.B inline length evaluation of Fig. 5 (// Run) + counterfactual instability of member c_coeff
    fig5_inline = score_steidl_inline_length("// Run")
    fig5_cf_run = score_steidl_member_comment("// Run", "run")["c_coeff"]
    fig5_cf_shutdown = score_steidl_member_comment("// Run", "shutdownServer")["c_coeff"]
    print(
        f"  [Sec. VI.B inline] steidl_fig5_trivial_inline   : words={fig5_inline['inline_word_count']} "
        f"| {fig5_inline['inline_length_class']} "
        f"(counterfactual c_coeff: run()={fig5_cf_run:.3f} vs shutdownServer()={fig5_cf_shutdown:.3f})"
    )
    assert fig5_inline["inline_word_count"] == 1 and fig5_cf_run == 1.0 and fig5_cf_shutdown == 0.0

    # Counterfactual misapplication of member-level c_coeff == 0 to substantive inline invariant comments
    inline_traps = [
        ("inline_trap_lock_contract", "// Caller must hold state_lock; timeout is in milliseconds and ties break by lowest term.", "tryAcquireLease", "if (now > deadline) return false;"),
        ("inline_trap_overflow_contract", "// Saturating add prevents wraparound past u32::MAX under concurrent retries.", "recordRetry", "count = count.saturating_add(1);"),
    ]
    p2a_traps: dict[str, object] = {}
    for label, cmt, fn, body in inline_traps:
        out = test_inline_c_coeff_misapplication(cmt, fn, body)
        p2a_traps[label] = out
        print(
            f"  [counterfactual  ] {label:29s}: misapplied_c_coeff={out['misapplied_member_c_coeff']:.3f} "
            f"| words={out['inline_word_count']:2d} | inv_hits={out['invariant_hits']} "
            f"| inline_false_alarm={out['inline_false_alarm']}"
        )
    assert p2a_traps["inline_trap_lock_contract"]["inline_false_alarm"] is True
    assert p2a_traps["inline_trap_overflow_contract"]["inline_false_alarm"] is True
    payload["probe_2a"] = {
        "member": p2a_member,
        "fig5_inline": fig5_inline,
        "fig5_counterfactual_c_coeff": {"run": fig5_cf_run, "shutdownServer": fig5_cf_shutdown},
        "inline_traps": p2a_traps,
    }

    print("\n================================================================================")
    print("PROBE 2B [exact arithmetic check on audited dataset counts; live CSV replay via --tian-csv]:")
    print("  Tian et al. (ICSE 2022, WhatMakesAGoodCM@2f7c1e33) 1,597-Commit & Verbatim-Regex Audit")
    print("================================================================================")
    tot_sampled = sum(r[2] for r in TIAN_2022_REPO_COUNTS)
    tot_multi = sum(r[3] for r in TIAN_2022_REPO_COUNTS)
    tot_l0 = sum(r[4] for r in TIAN_2022_REPO_COUNTS)
    tot_l3 = sum(r[5] for r in TIAN_2022_REPO_COUNTS)
    tot_l2 = sum(r[6] for r in TIAN_2022_REPO_COUNTS)
    tot_l1 = sum(r[7] for r in TIAN_2022_REPO_COUNTS)
    tot_atomic = tot_l0 + tot_l3 + tot_l2 + tot_l1
    assert tot_sampled == 1649 and tot_multi == 52 and tot_atomic == 1597
    assert (tot_l0, tot_l3, tot_l2, tot_l1) == (919, 426, 187, 65)

    unweighted = [0.0, 0.0, 0.0, 0.0]
    for rid, proj, samp, mult, l0, l3, l2, l1 in TIAN_2022_REPO_COUNTS:
        n_a = l0 + l3 + l2 + l1
        assert n_a == samp - mult
        pcts = (100.0 * l0 / n_a, 100.0 * l3 / n_a, 100.0 * l2 / n_a, 100.0 * l1 / n_a)
        for idx in range(4):
            unweighted[idx] += pcts[idx] / len(TIAN_2022_REPO_COUNTS)
        print(
            f"  repo_id={rid} ({proj:27s}, n={n_a:3d}): "
            f"Both={pcts[0]:5.2f}% NoWhy={pcts[1]:5.2f}% NoWhat={pcts[2]:5.2f}% Neither={pcts[3]:4.2f}%"
        )
    pooled_deficit = 100.0 * (tot_l3 + tot_l2 + tot_l1) / tot_atomic
    no_why_ratio = tot_l3 / tot_l2
    print(
        f"  POOLED (n={tot_atomic}): Both={100*tot_l0/tot_atomic:.2f}% NoWhy={100*tot_l3/tot_atomic:.2f}% "
        f"NoWhat={100*tot_l2/tot_atomic:.2f}% Neither={100*tot_l1/tot_atomic:.2f}% | "
        f"Deficit={pooled_deficit:.2f}% | NoWhy/NoWhat={no_why_ratio:.2f}x"
    )
    print(
        f"  UNWEIGHTED 5-REPO MEAN: Both={unweighted[0]:.2f}% NoWhy={unweighted[1]:.2f}% "
        f"NoWhat={unweighted[2]:.2f}% Neither={unweighted[3]:.2f}% | Deficit={sum(unweighted[1:]):.2f}%"
    )
    why_pos_n = sum(r[2] for r in TIAN_2022_MARKER_AUDIT if r[0] in (0, 2))
    marker_summary: dict[str, dict[str, float | int]] = {}
    for name, col_idx in (("WHY_CLAUSE_REGEX", 3), ("ISSUE_REF_REGEX", 4), ("UNION", 5)):
        tp = sum(r[col_idx] for r in TIAN_2022_MARKER_AUDIT if r[0] in (0, 2))
        fp = sum(r[col_idx] for r in TIAN_2022_MARKER_AUDIT if r[0] in (1, 3))
        prec = round(100.0 * tp / (tp + fp), 2)
        rec = round(100.0 * tp / why_pos_n, 2)
        marker_summary[name] = {"tp": tp, "fp": fp, "precision_pct": prec, "recall_pct": rec}
        print(f"  1,597-commit {name:16s}: TP={tp:3d} FP={fp:2d} prec={prec:5.2f}% rec={rec:5.2f}%")
    print(f"  ISSUE_REF_REGEX share in Why+What: 551/919 = {100*551/919:.2f}% | in Why-Only: 85/187 = {100*85/187:.2f}%")
    if args.tian_csv is not None:
        live = replay_tian_csv(args.tian_csv)
        print(f"  LIVE CSV VERIFICATION PASSED: {live}")
    assert abs(pooled_deficit - 42.45) < 0.02 and no_why_ratio > 2.2
    payload["probe_2b"] = {
        "pooled_counts": {"both": tot_l0, "no_why": tot_l3, "no_what": tot_l2, "neither": tot_l1},
        "pooled_deficit_pct": round(pooled_deficit, 2),
        "unweighted_deficit_pct": round(sum(unweighted[1:]), 2),
        "no_why_to_no_what_ratio": round(no_why_ratio, 2),
        "marker_summary": marker_summary,
    }

    print("\n================================================================================")
    print("PROBE 2C [minimal lexical-stem mechanism illustration; not a production detector]:")
    print("  Diff-Only vs. Issue-Grounded Commit Why Audit (Including Lexical Boundary Cases)")
    print("================================================================================")
    sample_diff = (
        "- if (retry_count > MAX_RETRIES) return Err(Timeout);\n"
        "+ if (retry_count >= MAX_RETRIES) return Err(Timeout);\n"
    )
    sample_issue = (
        "Issue #412: Off-by-one retry bound allows 4 attempts instead of configured 3 "
        "under SLA budget, violating idempotency test."
    )
    commit_cases = [
        ("what_only_no_why", "Change retry_count comparison from > to >= MAX_RETRIES."),
        ("diff_only_hallucinated_why", "Change retry_count >= MAX_RETRIES to prevent stack overflow crash in recursive parser."),
        ("issue_grounded_what_and_why", "Change retry_count >= MAX_RETRIES so that attempts respect the configured SLA budget and idempotency test."),
        ("boundary_paraphrase_fp", "Change retry_count >= MAX_RETRIES because 4 tries breach our service latency cap."),
        ("boundary_bare_issue_link", "Enforce 3-attempt SLA retry bound (#412)."),
    ]
    p2c_res: dict[str, object] = {}
    for tag, msg in commit_cases:
        res = audit_commit_why_grounding(sample_diff, sample_issue, msg)
        p2c_res[tag] = res
        print(f"  {tag:28s}: {res}")
    assert p2c_res["diff_only_hallucinated_why"]["unverified_why_hallucination"] is True
    assert p2c_res["issue_grounded_what_and_why"]["unverified_why_hallucination"] is False
    assert p2c_res["boundary_paraphrase_fp"]["unverified_why_hallucination"] is True
    assert p2c_res["boundary_bare_issue_link"]["has_why"] is False and p2c_res["boundary_bare_issue_link"]["has_issue_ref"] is True
    payload["probe_2c"] = p2c_res

    print("\n================================================================================")
    print("PROBE 3A [exact reproduction of pinned repository logic] + [exact calculation on published dataset]:")
    print("  LIBRO (coinse/libro@645473db) Defects4J (570 FIB) & GHRB (25 FIB) Exact Replay")
    print("================================================================================")
    d4j_total = sum(n for _, n, _ in LIBRO_D4J_MAX_CLUSTER_FREQ)
    d4j_repro = sum(p for _, _, p in LIBRO_D4J_MAX_CLUSTER_FREQ)
    d4j_auc = compute_roc_auc_from_freq(LIBRO_D4J_MAX_CLUSTER_FREQ)
    print(f"  Defects4J (570 FIB bugs, {d4j_repro} reproduced): exact ROC AUC = {d4j_auc:.4f}")
    assert d4j_total == 570 and d4j_repro == 251 and abs(d4j_auc - 0.8185) < 0.0005
    d4j_sweep: dict[str, object] = {}
    for th in (0, 1, 2, 3, 4, 5, 10):
        sel_n = sum(n for s, n, _ in LIBRO_D4J_MAX_CLUSTER_FREQ if s > th)
        rep_n = sum(p for s, _, p in LIBRO_D4J_MAX_CLUSTER_FREQ if s > th)
        d4j_sweep[f"T>{th}"] = {
            "selected": sel_n,
            "reproduced": rep_n,
            "precision": round(rep_n / sel_n, 4),
            "pool_recall": round(rep_n / d4j_repro, 4),
        }
        print(
            f"    D4J T_aggr>{th:2d}: selected={sel_n:3d} reproduced={rep_n:3d} "
            f"precision={rep_n/sel_n:.4f} pool_recall={rep_n/d4j_repro:.4f}"
        )
    assert (d4j_sweep["T>1"]["selected"], d4j_sweep["T>1"]["reproduced"]) == (350, 219)

    ghrb_freq_map: dict[int, list[int]] = defaultdict(lambda: [0, 0])
    for _, clus in LIBRO_GHRB_CLUSTERS:
        m = max(c[0] for c in clus)
        y = 1 if any(mem[2] == 1 for _, _, mems in clus for mem in mems) else 0
        ghrb_freq_map[m][0] += 1
        ghrb_freq_map[m][1] += y
    ghrb_auc = compute_roc_auc_from_freq([(k, v[0], v[1]) for k, v in sorted(ghrb_freq_map.items())])
    ghrb_th0_rr, ranks_th0_rr = replay_libro_clusters(LIBRO_GHRB_CLUSTERS, 0, True)
    ghrb_th0_no, ranks_th0_no = replay_libro_clusters(LIBRO_GHRB_CLUSTERS, 0, False)
    ghrb_th1_rr, _ = replay_libro_clusters(LIBRO_GHRB_CLUSTERS, 1, True)
    ghrb_th1_no, _ = replay_libro_clusters(LIBRO_GHRB_CLUSTERS, 1, False)

    # Order-invariance verification under full reversal of cluster and intra-cluster orders
    reversed_ghrb = tuple(
        (bid, tuple((csize, brm, tuple(reversed(mems))) for csize, brm, mems in reversed(clus)))
        for bid, clus in LIBRO_GHRB_CLUSTERS
    )
    _, ranks_th0_rev = replay_libro_clusters(reversed_ghrb, 0, True)
    assert ranks_th0_rr == ranks_th0_rev, "GHRB ranks must be invariant to input cluster/member ordering"

    print(f"  GHRB (25 FIB bugs, 10 reproduced): exact ROC AUC = {ghrb_auc:.4f} | order_invariant=True")
    print(f"    GHRB T_aggr>0 round_robin=True : {ghrb_th0_rr}")
    print(f"    GHRB T_aggr>0 round_robin=False: {ghrb_th0_no}")
    print(f"    GHRB T_aggr>1 round_robin=True : {ghrb_th1_rr}")
    print(f"    GHRB T_aggr>1 round_robin=False: {ghrb_th1_no}")
    rescued = [
        (bid, ranks_th0_rr[bid], ranks_th0_no[bid])
        for bid in sorted(ranks_th0_rr.keys())
        if ranks_th0_rr[bid] != ranks_th0_no[bid]
    ]
    print(f"    Real GHRB bugs rescued by L144-147 round-robin: {rescued}")
    assert abs(ghrb_auc - 0.7867) < 0.0005
    assert (ghrb_th0_rr["acc@1"], ghrb_th0_rr["acc@3"], ghrb_th0_rr["acc@5"]) == (6.0, 8.0, 9.0)
    assert (ghrb_th1_rr["selected"], ghrb_th1_rr["reproduced"], ghrb_th1_rr["acc@5"]) == (21.0, 9.0, 8.0)
    assert (ghrb_th1_no["acc@5"], ghrb_th1_rr["acc@5"]) == (6.0, 8.0)
    assert rescued == [("jhy_jsoup-1648", 2, 10), ("jhy_jsoup-1763", 4, 14)]
    payload["probe_3a"] = {
        "d4j_auc": round(d4j_auc, 4),
        "d4j_sweep": d4j_sweep,
        "ghrb_auc": round(ghrb_auc, 4),
        "ghrb_th0_rr": ghrb_th0_rr,
        "ghrb_th0_no": ghrb_th0_no,
        "ghrb_th1_rr": ghrb_th1_rr,
        "ghrb_th1_no": ghrb_th1_no,
        "rescued": rescued,
    }

    print("\n================================================================================")
    print("PROBE 3B [parametric stress harness; subordinated to real Probe 3A replay]:")
    print("  LIBRO Threshold Sweep & Round-Robin Rescue on Seeded 200-Bug Stress Harness")
    print("================================================================================")
    syn = build_synthetic_libro_dataset(seed=42, n_bugs=200, samples_per_bug=50)
    prev_prec = 0.0
    p3b_sweep: dict[str, object] = {}
    for thr in (0, 1, 2, 3, 5):
        res_s, _ = replay_libro_clusters(syn, thr, True)
        p3b_sweep[f"T>{thr}_rr"] = res_s
        print(f"  Synthetic (T_aggr>{thr}, round_robin=True) : {res_s}")
        assert res_s["precision"] >= prev_prec
        prev_prec = res_s["precision"]
    syn_rr1, _ = replay_libro_clusters(syn, 1, True)
    syn_no1, _ = replay_libro_clusters(syn, 1, False)
    p3b_sweep["T>1_no_rr"] = syn_no1
    print(f"  Synthetic (T_aggr>1, round_robin=False): {syn_no1}")
    assert syn_rr1["acc@3"] > syn_no1["acc@3"] and syn_rr1["mean_wasted@5"] < syn_no1["mean_wasted@5"]
    payload["probe_3b"] = p3b_sweep

    print("\n================================================================================")
    print("PROBE 3C [derived arithmetic check on published Table 1-3 summary rates]:")
    print("  Yu et al. (2026, arXiv:2606.22711v1) Human Co-Authored-By Audit (33,596 AI-Agent PRs)")
    print("================================================================================")
    yu = verify_yu_2026_tables()
    print(
        f"  Total AI-Agent PRs={yu['total_prs']} (Codex share={yu['codex_share_pct']}%) | "
        f"Table 1 exact n: human_coauth={yu['table1_n_human_coauth']} vs pure_agent={yu['table1_n_pure_agent']} "
        f"(Yates chi2={yu['table1_chi2_yates']:.2f} [Table 1 printed: 2424], Pearson chi2={yu['table1_chi2_pearson']:.2f})"
    )
    print(
        f"  Table 2 1-decimal reconstruction: n_coauth={yu['reconstructed_n_human_coauth']} vs n_pure={yu['reconstructed_n_pure_agent']} | "
        f"Pooled MR: {yu['reconstructed_pooled_mr_coauth_pct']}% vs {yu['reconstructed_pooled_mr_pure_pct']}% "
        f"(Delta={yu['reconstructed_pooled_delta_pp']:+.2f} pp) | excluding_Codex={yu['excluding_codex_pooled_delta_pp']:+.2f} pp"
    )
    print(
        f"  Within-agent Deltas (pp): published={yu['published_within_deltas_pp']} | "
        f"1-dec_reconstructed={yu['reconstructed_within_deltas_pp']} | "
        f"positive={yu['positive_within_agent_count']}/5 | unweighted_pub_mean={yu['unweighted_published_within_mean_pp']:+.2f} pp"
    )
    print(f"  Table 3 collaboration modes (n={yu['table3_total_prs']}): {yu['table3_modes']}")
    assert yu["total_prs"] == 33596
    assert abs(float(yu["table1_chi2_yates"]) - 2424.04) < 0.05
    assert float(yu["reconstructed_pooled_delta_pp"]) < -25.0
    assert yu["positive_within_agent_count"] == 4
    assert float(yu["excluding_codex_pooled_delta_pp"]) > 20.0
    payload["probe_3c"] = yu

    canonical_json = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    payload_sha256 = hashlib.sha256(canonical_json).hexdigest()
    print(
        f"\nALL PROBES PASSED DETERMINISTICALLY (0 failures, "
        f"payload_sha256_12={payload_sha256[:12]}, payload_sha256={payload_sha256})."
    )


if __name__ == "__main__":
    main()
