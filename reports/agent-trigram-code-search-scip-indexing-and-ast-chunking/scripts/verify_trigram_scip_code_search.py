#!/usr/bin/env python3
"""Deterministic verification probe for trigram code search, SCIP/LSIF indexing,
AST-aware code chunking, hybrid retrieval fusion, and Git Merkle invalidation.

Covers five verification suites using Python 3.10+ standard library only (plus
hermetic local `git` CLI inside `tempfile.TemporaryDirectory()` for Suite 5):
  1. Russ Cox (2012) 5-attribute inductive regex-to-trigram boolean compiler
     and `sourcegraph/zoekt@b55ce727` 63-bit UTF-8 rune trigrams, sparse
     `makeRuneOffsetMap` (freq=100), `unicode.SimpleFold` `generateCaseNgrams`
     (8 on `"foo"`, 27 on `"ksk"`, and 64 on `"\u1fbe\u1fbe\u1fbe"`) vs.
     ASCII-only `LowerRegexp`, 2-anchor `findSelectiveNgrams` +
     `distanceHitIterator`, `OpRepeat` (`eval.go:639-650`), `<3`-rune
     content/filename (`matchtree.go:1334`) vs. symbol (`matchtree.go:1205`)
     selectivity collapse, and constant-IDF + shard-local `averageFileLength`
     drift in `scoreFileBM25`.
  2. `sourcegraph/scip@8fe50375` Protobuf wire encoder (`Metadata` fields 1..4
     with `text_document_encoding = 4`, per-`Document` `position_encoding = 6`
     per `scip.proto:53, 118`) & `ParseStreaming`
     (`bindings/go/scip/parse.go:29-122`) vs. Microsoft `LSIF v0.5.0` JSON-Lines
     property-graph explosion (`shard`-tagged `item` edges) and `PositionEncoding`
     UTF-8 / UTF-16 / UTF-32 column offset slicing traps (`scip.proto:122-146`).
  3. `yilinjz/astchunk@82029ada` (`cAST`) Split-then-Merge vs. Split-Only vs.
     fixed-line chunking (modeled over stdlib `ast` statement-flattened nodes as
     a pure-Python surrogate for `tree-sitter-python`'s `block`-wrapped CST,
     noting upstream `pyrsistent.v` ancestor vectors at `astchunk_builder.py:72,122`),
     paper Algorithm 1 missing-`else` node drop, all five `astchunk`
     implementation defects (UTF-8 byte-vs-char miscount, `\t -> " "`
     `rebuild_code` corruption, Python-only ancestors + `filepath` cache busting,
     oversized leaf deletion, `chunk_overlap` overflow), and live harness bugs
     in `CoSQA_Plus@1ca33438`, `repobench@e0cfd34c`, and `code-rag-bench@f9e100ca`.
  4. Hybrid lexical-dense retrieval fusion: `Bruch et al. (ACM TOIS 2023/2024)`
     Lemma 4.2 single-query affine rank-equivalence (`M2C2` == `TM2C2` == `Z-Score`),
     `§4.2` / `Table 2` validation-tuned `alpha = 0.80` (`alpha in [0.6, 0.8]` in `§7`),
     `§5.2` Lipschitz continuity step-jump analysis, and `Cormack et al. (SIGIR 2009)`
     `RRF(k=60)` vs. convex score normalizations across an explicitly labeled
     `[illustrative analytical model]` spanning exact-symbol margins, narrow-band
     noise (`m_q approx M_q`), and heavy-tailed boilerplate BM25 outliers
     (`M_q >> s_(2)`), plus primary-table audits.
  5. Real `git` Merkle-tree (`fast-import`, `rev-parse`, `diff-tree -r`,
     `status --porcelain -z`) incremental index invalidation over a 1,024-file
     repository vs. default `zoekt-git-index` (`IsDelta=false`, `builder.go:433`)
     whole-shard rebuild (alongside opt-in `--delta` / `FileTombstones` constraints),
     `>64`-branch `uint64` bitmask overflow, and a two-layer dirty-worktree
     tombstone/overlay index.

Execution invariants:
  - Python 3.10+ stdlib only; zero third-party packages; zero network I/O.
  - All temporary files isolated in `with tempfile.TemporaryDirectory():`.
  - Zero local paths or wall-clock timestamps in stdout; bit-identical across
    `PYTHONHASHSEED=1` and `PYTHONHASHSEED=2` with `python3 -I -B`.
"""

from __future__ import annotations

import ast
import bisect
from dataclasses import dataclass
import gzip
import hashlib
import io
import json
import math
import os
import re
import string
import subprocess
import tempfile
from typing import Optional


# ============================================================================
# PROBE 1: Russ Cox (2012) Trigram Compiler & sourcegraph/zoekt@b55ce727 Engine
# ============================================================================


@dataclass(frozen=True)
class TrigramQuery:
    """Boolean trigram query AST (`ANY`, `NONE`, `LIT`, `AND`, `OR`) per
    Russ Cox, 'Regular Expression Matching with a Trigram Index' (Jan 2012).
    """

    op: str  # "ANY" | "NONE" | "LIT" | "AND" | "OR"
    trigram: str = ""
    children: tuple["TrigramQuery", ...] = ()


Q_ANY = TrigramQuery("ANY")
Q_NONE = TrigramQuery("NONE")


def q_lit(tri: str) -> TrigramQuery:
    assert len(tri) == 3
    return TrigramQuery("LIT", trigram=tri)


def q_and(*qs: TrigramQuery) -> TrigramQuery:
    flat: list[TrigramQuery] = []
    seen: set[TrigramQuery] = set()
    for q in qs:
        if q.op == "NONE":
            return Q_NONE
        if q.op == "ANY":
            continue
        items = q.children if q.op == "AND" else (q,)
        for item in items:
            if item not in seen:
                seen.add(item)
                flat.append(item)
    if not flat:
        return Q_ANY
    if len(flat) == 1:
        return flat[0]
    return TrigramQuery("AND", children=tuple(flat))


def q_or(*qs: TrigramQuery) -> TrigramQuery:
    flat: list[TrigramQuery] = []
    seen: set[TrigramQuery] = set()
    for q in qs:
        if q.op == "ANY":
            return Q_ANY
        if q.op == "NONE":
            continue
        items = q.children if q.op == "OR" else (q,)
        for item in items:
            if item not in seen:
                seen.add(item)
                flat.append(item)
    if not flat:
        return Q_NONE
    if len(flat) == 1:
        return flat[0]
    return TrigramQuery("OR", children=tuple(flat))


def trigrams_of_string(s: str) -> TrigramQuery:
    """Extracts conjunction of all 3-rune substrings of `s` (`ANY` if `len(s)<3`)."""
    if len(s) < 3:
        return Q_ANY
    return q_and(*(q_lit(s[i : i + 3]) for i in range(len(s) - 2)))


def trigrams_of_set(strings: set[str] | tuple[str, ...]) -> TrigramQuery:
    """Disjunction over `s in strings` of `trigrams_of_string(s)`."""
    if not strings:
        return Q_NONE
    return q_or(*(trigrams_of_string(s) for s in sorted(strings)))


@dataclass(frozen=True)
class RegexNode:
    """Minimal regular expression AST for Cox (2012) & Zoekt `eval.go`."""

    op: str  # "EMPTY" | "LIT" | "CLASS" | "QUEST" | "STAR" | "PLUS" | "REPEAT" | "ALT" | "CONCAT"
    text: str = ""
    subs: tuple["RegexNode", ...] = ()
    min_rep: int = 0
    max_rep: int = 0  # -1 for unbounded `{m,}`


@dataclass
class CoxInfo:
    """Russ Cox (2012) 5-attribute inductive regex analysis state."""

    emptyable: bool
    exact: Optional[set[str]]  # None represents `unknown`
    prefix: set[str]
    suffix: set[str]
    match: TrigramQuery


def _trim_prefix_set(s: set[str]) -> set[str]:
    """Information-discarding reduction: if `u` is a prefix of `v`, discard `v`."""
    ordered = sorted(s, key=lambda x: (len(x), x))
    kept: list[str] = []
    for item in ordered:
        if not any(item.startswith(p) for p in kept):
            kept.append(item)
    return set(kept)


def _trim_suffix_set(s: set[str]) -> set[str]:
    """Information-discarding reduction: if `u` is a suffix of `v`, discard `v`."""
    ordered = sorted(s, key=lambda x: (len(x), x))
    kept: list[str] = []
    for item in ordered:
        if not any(item.endswith(p) for p in kept):
            kept.append(item)
    return set(kept)


def _bound_cox_info(info: CoxInfo, max_exact: int = 8, max_affix: int = 8) -> CoxInfo:
    """Applies Russ Cox's information-saving rules BEFORE information-discarding
    set reductions whenever `exact`, `prefix`, or `suffix` exceeds cardinality bounds.
    """
    if info.exact is not None:
        info.match = q_and(info.match, trigrams_of_set(info.exact))
        if len(info.exact) > max_exact:
            info.exact = None

    info.prefix = _trim_prefix_set(info.prefix)
    while len(info.prefix) > max_affix:
        info.match = q_and(info.match, trigrams_of_set(info.prefix))
        max_len = max(len(x) for x in info.prefix)
        if max_len == 0:
            break
        info.prefix = _trim_prefix_set(
            {x[:-1] if len(x) == max_len else x for x in info.prefix}
        )

    info.suffix = _trim_suffix_set(info.suffix)
    while len(info.suffix) > max_affix:
        info.match = q_and(info.match, trigrams_of_set(info.suffix))
        max_len = max(len(x) for x in info.suffix)
        if max_len == 0:
            break
        info.suffix = _trim_suffix_set(
            {x[1:] if len(x) == max_len else x for x in info.suffix}
        )

    info.match = q_and(
        info.match,
        trigrams_of_set(info.prefix),
        trigrams_of_set(info.suffix),
    )
    return info


def compile_cox_trigram(node: RegexNode, max_set: int = 8) -> CoxInfo:
    """Faithful port of Russ Cox (2012) inductive 5-attribute regex analyzer."""
    if node.op == "EMPTY":
        return CoxInfo(True, {""}, {""}, {""}, Q_ANY)
    if node.op == "LIT":
        if node.text == "":
            return CoxInfo(True, {""}, {""}, {""}, Q_ANY)
        s = node.text
        return _bound_cox_info(
            CoxInfo(False, {s}, {s}, {s}, trigrams_of_string(s)),
            max_set,
            max_set,
        )
    if node.op == "CLASS":
        chars = set(node.text)
        return _bound_cox_info(
            CoxInfo(False, chars, set(chars), set(chars), Q_ANY),
            max_set,
            max_set,
        )
    if node.op == "QUEST":
        sub = compile_cox_trigram(node.subs[0], max_set)
        ex = (sub.exact | {""}) if sub.exact is not None else None
        return CoxInfo(True, ex, {""}, {""}, Q_ANY)
    if node.op == "STAR":
        return CoxInfo(True, None, {""}, {""}, Q_ANY)
    if node.op == "PLUS":
        sub = compile_cox_trigram(node.subs[0], max_set)
        return _bound_cox_info(
            CoxInfo(sub.emptyable, None, set(sub.prefix), set(sub.suffix), sub.match),
            max_set,
            max_set,
        )
    if node.op == "REPEAT":
        unit = node.subs[0]
        parts: list[RegexNode] = [unit for _ in range(node.min_rep)]
        if node.max_rep < 0:
            parts.append(RegexNode("STAR", subs=(unit,)))
        elif node.max_rep > node.min_rep:
            parts.extend(RegexNode("QUEST", subs=(unit,)) for _ in range(node.max_rep - node.min_rep))
        if not parts:
            return CoxInfo(True, {""}, {""}, {""}, Q_ANY)
        if len(parts) == 1:
            return compile_cox_trigram(parts[0], max_set)
        return compile_cox_trigram(RegexNode("CONCAT", subs=tuple(parts)), max_set)
    if node.op == "ALT":
        infos = [compile_cox_trigram(s, max_set) for s in node.subs]
        emp = any(i.emptyable for i in infos)
        if all(i.exact is not None for i in infos):
            ex: Optional[set[str]] = set().union(*(i.exact for i in infos if i.exact is not None))
        else:
            ex = None
        pref = set().union(*(i.prefix for i in infos))
        suff = set().union(*(i.suffix for i in infos))
        m = q_or(*(i.match for i in infos))
        return _bound_cox_info(CoxInfo(emp, ex, pref, suff, m), max_set, max_set)
    if node.op == "CONCAT":
        cur = compile_cox_trigram(node.subs[0], max_set)
        for nxt_node in node.subs[1:]:
            nxt = compile_cox_trigram(nxt_node, max_set)
            cross_mid = {a + b for a in cur.suffix for b in nxt.prefix}
            m = q_and(cur.match, nxt.match, trigrams_of_set(cross_mid))
            emp = cur.emptyable and nxt.emptyable
            if cur.exact is not None and nxt.exact is not None:
                # Save cross-product trigrams BEFORE discarding large exact set
                cross_ex = {a + b for a in cur.exact for b in nxt.exact}
                m = q_and(m, trigrams_of_set(cross_ex))
                ex = cross_ex if len(cross_ex) <= max_set else None
            else:
                ex = None

            if cur.exact is not None:
                pref = {a + b for a in cur.exact for b in nxt.prefix}
            elif cur.emptyable:
                pref = cur.prefix | nxt.prefix
            else:
                pref = set(cur.prefix)

            if nxt.exact is not None:
                suff = {a + b for a in cur.suffix for b in nxt.exact}
            elif nxt.emptyable:
                suff = nxt.suffix | cur.suffix
            else:
                suff = set(nxt.suffix)

            cur = _bound_cox_info(CoxInfo(emp, ex, pref, suff, m), max_set, max_set)
        return cur
    raise ValueError(f"Unsupported RegexNode op: {node.op}")


def compile_zoekt_matchtree_query(node: RegexNode, min_text_size: int = 3) -> TrigramQuery:
    """Faithful port of `regexpToMatchTreeRecursive` (`index/eval.go:621-698`)
    at `sourcegraph/zoekt@b55ce727df8cfbed76b8a1420445fd0cf93f3256`.
    Note how Zoekt does NOT track `suffix(e1) x prefix(e2)` cross-boundary
    trigrams, handles `OpRepeat` (`eval.go:639-650`) solely by recursing on
    `r.Sub[0]` when `r.Min >= 1`, and collapses `OpAlternate` to
    `bruteForceMatchTree` (`Q_ANY`) whenever any branch is `< minTextSize`
    (`eval.go:687-690`). Top-level `<3`-rune content/filename `Substring`
    queries convert to `bruteForceMatchTree` at `matchtree.go:1334-1341`
    (whereas `<3`-rune `Symbol` substring queries convert to
    `newSymbolRegexpMatchTree` at `matchtree.go:1205-1212`, scanning every
    document's ctags symbol table).
    """
    if node.op == "LIT":
        if len(node.text) >= min_text_size:
            return trigrams_of_string(node.text)
        return Q_ANY  # falls through to bruteForceMatchTree (`eval.go:699`)
    if node.op == "PLUS":
        return compile_zoekt_matchtree_query(node.subs[0], min_text_size)
    if node.op == "REPEAT":
        if node.min_rep >= 1:
            return compile_zoekt_matchtree_query(node.subs[0], min_text_size)
        return Q_ANY
    if node.op in ("EMPTY", "CLASS", "QUEST", "STAR"):
        return Q_ANY
    if node.op == "CONCAT":
        qs = [compile_zoekt_matchtree_query(s, min_text_size) for s in node.subs]
        non_bf = [q for q in qs if q.op != "ANY"]
        if not non_bf:
            return Q_ANY
        return q_and(*non_bf)
    if node.op == "ALT":
        qs = [compile_zoekt_matchtree_query(s, min_text_size) for s in node.subs]
        for q in qs:
            if q.op == "ANY":
                return Q_ANY
        return q_or(*qs)
    raise ValueError(f"Unsupported op: {node.op}")


# --- Zoekt `bits.go`, `shard_builder.go`, `indexdata.go`, `hititer.go`, `score.go` ---

RUNE_MASK = (1 << 21) - 1
RUNE_OFFSET_FREQUENCY = 100
TRIGRAM_MAX_DEFAULT = 20000


def runes_to_ngram(r0: str, r1: str, r2: str) -> int:
    """Port of `runesToNGram` (`index/bits.go:171-173`)."""
    return (ord(r0) << 42) | (ord(r1) << 21) | ord(r2)


def ngram_to_runes(ng: int) -> tuple[str, str, str]:
    """Port of `ngramToRunes` (`index/bits.go:190-192`)."""
    return (
        chr((ng >> 42) & RUNE_MASK),
        chr((ng >> 21) & RUNE_MASK),
        chr(ng & RUNE_MASK),
    )


def make_rune_offset_map(sampled_byte_offsets: list[int]) -> list[tuple[int, int]]:
    """Port of `makeRuneOffsetMap` (`index/bits.go:467-480`).
    Elides every entry where `byteOffset == expected` (0 bytes for pure ASCII).
    """
    expected = 0
    out: list[tuple[int, int]] = []
    for idx, byte_off in enumerate(sampled_byte_offsets):
        if byte_off != expected:
            out.append((idx * RUNE_OFFSET_FREQUENCY, byte_off))
            expected = byte_off
        expected += RUNE_OFFSET_FREQUENCY
    return out


def lookup_rune_offset(
    offset_map: list[tuple[int, int]], corpus_bytes: bytes, rune_offset: int
) -> int:
    """Port of `runeOffsetMap.lookup` (`index/bits.go:487-508`) plus `left`-rune
    UTF-8 advance to recover exact byte offset.
    """
    left = rune_offset % RUNE_OFFSET_FREQUENCY
    block_rune = rune_offset - left
    if not offset_map:
        byte_off = block_rune
    else:
        # Find last index `idx` with `offset_map[idx][0] <= block_rune`
        keys = [rc[0] for rc in offset_map]
        idx = bisect.bisect_right(keys, block_rune) - 1
        if idx >= 0:
            r_base, b_base = offset_map[idx]
            byte_off = b_base + (block_rune - r_base)
        else:
            byte_off = block_rune

    # Advance `left` UTF-8 code points from `byte_off`
    pos = byte_off
    for _ in range(left):
        b0 = corpus_bytes[pos]
        if b0 < 0x80:
            pos += 1
        elif (b0 & 0xE0) == 0xC0:
            pos += 2
        elif (b0 & 0xF0) == 0xE0:
            pos += 3
        else:
            pos += 4
    return pos


# Exact Unicode SimpleFold cycles across all Unicode scalar values (BMP + SMP).
# Matches Go's `unicode.SimpleFold` (`unicode/letter.go`), including 3-element
# Kelvin/long-s orbits (`3^3 = 27` on `"ksk"`) and 4-element Greek prosgegrammeni
# `[U+0345, U+0399, U+03B9, U+1FBE]` (`4^3 = 64` on `"\u1fbe\u1fbe\u1fbe"`).
def _build_simple_fold_map() -> dict[str, str]:
    """Builds exact `unicode.SimpleFold` cycle map over Unicode scalar values
    `U+0001..U+10FFFF` (skipping UTF-16 surrogates `U+D800..U+DFFF`).
    """
    groups: dict[str, list[int]] = {}
    for cp in range(0x0001, 0x110000):
        if 0xD800 <= cp <= 0xDFFF:
            continue
        ch = chr(cp)
        cf = ch.casefold()
        if len(cf) == 1 and (ch != cf or ch.upper() != ch or ch.lower() != ch):
            groups.setdefault(cf, []).append(cp)
    fold_next: dict[str, str] = {}
    for cps in groups.values():
        if len(cps) >= 2:
            cps_sorted = sorted(cps)
            for i, cp in enumerate(cps_sorted):
                fold_next[chr(cp)] = chr(cps_sorted[(i + 1) % len(cps_sorted)])
    return fold_next


SIMPLE_FOLD_NEXT = _build_simple_fold_map()


def simple_fold(ch: str) -> str:
    return SIMPLE_FOLD_NEXT.get(ch, ch)


def generate_case_ngrams(ng: int) -> list[int]:
    """Exact port of `generateCaseNgrams` (`index/bits.go:27-48`)."""
    as_runes = list(ngram_to_runes(ng))
    cur = list(as_runes)
    variants: list[int] = []
    while True:
        for i in range(3):
            nxt = simple_fold(cur[i])
            cur[i] = nxt
            if nxt != as_runes[i]:
                break
        variants.append(runes_to_ngram(cur[0], cur[1], cur[2]))
        if cur == as_runes:
            break
    return variants


def zoekt_query_lower_regexp_literal(lit: str) -> str:
    """Exact port of `query.LowerRegexp` (`query/regexp.go:26-46`): folds ONLY
    ASCII `'A'..'Z'`, leaving non-ASCII uppercase/Kelvin `'K'` untouched.
    """
    return "".join(
        chr(ord(c) + ord("a") - ord("A")) if "A" <= c <= "Z" else c for c in lit
    )


def find_selective_ngrams(
    pattern: str, posting_sizes: dict[int, int]
) -> tuple[tuple[int, int], tuple[int, int]]:
    """Exact port of `iterateNgrams` + `findSelectiveNgrams` +
    `minFrequencyNgramOffsets` (`index/indexdata.go:357-476`).
    Returns `((first_index, first_ng), (last_index, last_ng))`.
    """
    ngram_offs = [
        (i, runes_to_ngram(pattern[i], pattern[i + 1], pattern[i + 2]))
        for i in range(len(pattern) - 2)
    ]
    # `slices.SortFunc(ngramOffs, runeNgramOff.Compare)` sorts by `(ngram, index)`
    ngram_offs_sorted = sorted(ngram_offs, key=lambda x: (x[1], x[0]))
    frequencies = [posting_sizes.get(ng, 0) for _, ng in ngram_offs_sorted]
    index_map = {orig_idx: sorted_i for sorted_i, (orig_idx, _) in enumerate(ngram_offs_sorted)}

    idx0, idx1 = 0, 0
    min0, min1 = (1 << 32) - 1, (1 << 32) - 1
    for i, freq in enumerate(frequencies):
        if freq <= min0:
            idx0, idx1 = i, idx0
            min0, min1 = freq, min0
        elif freq <= min1:
            idx1 = i
            min1 = freq

    c0 = ngram_offs_sorted[idx0]
    c1 = ngram_offs_sorted[idx1]
    first, last = (c0, c1) if c0[0] <= c1[0] else (c1, c0)

    if last[0] - first[0] < 3:
        new_first_idx = max(last[0] - 3, 0)
        if new_first_idx != first[0]:
            first = ngram_offs_sorted[index_map[new_first_idx]]
        new_last_idx = min(first[0] + 3, len(ngram_offs_sorted) - 1)
        if new_last_idx != last[0]:
            last = ngram_offs_sorted[index_map[new_last_idx]]
    return first, last


def distance_hit_intersect(postings_1: list[int], postings_2: list[int], dist: int) -> list[int]:
    """Exact port of `distanceHitIterator` (`index/hititer.go:51-93`):
    two-pointer leapfrog intersection checking `p1 + dist == p2`.
    """
    hits: list[int] = []
    i, j = 0, 0
    n1, n2 = len(postings_1), len(postings_2)
    while i < n1 and j < n2:
        p1, p2 = postings_1[i], postings_2[j]
        if p1 + dist < p2:
            i = bisect.bisect_left(postings_1, p2 - dist, i + 1)
        elif p1 + dist > p2:
            j = bisect.bisect_left(postings_2, p1 + dist, j + 1)
        else:
            hits.append(p1)
            i += 1
            j += 1
    return hits


def zoekt_bm25_file_score(
    term_freqs: dict[str, int],
    file_byte_len: int,
    shard_doc_byte_lens: list[int],
    global_avg_override: float = 0.0,
) -> float:
    """Exact port of `scoreFileBM25` + `sumTFScores` + `tfScore`
    (`index/score.go:263-282, 398-425`).
    Notice TWO upstream behaviors:
      1. `IDF` is omitted (treated as constant `1.0` for all terms).
      2. When `BM25AverageFileLength <= 0`, `averageFileLength` defaults to
         the SHARD-LOCAL byte mean `sum(shard_bytes) / numDocs`.
    """
    k, b = 1.2, 0.75
    avg_len = (
        global_avg_override
        if global_avg_override > 0.0
        else (sum(shard_doc_byte_lens) / len(shard_doc_byte_lens))
    )
    if avg_len == 0.0:
        avg_len = 1.0
    length_ratio = file_byte_len / avg_len
    return sum(
        ((k + 1.0) * f) / (k * (1.0 - b + b * length_ratio) + f)
        for f in sorted(term_freqs.values())
        if f > 0
    )


def eval_trigram_query_on_doc(q: TrigramQuery, doc_trigrams: set[str]) -> bool:
    if q.op == "ANY":
        return True
    if q.op == "NONE":
        return False
    if q.op == "LIT":
        return q.trigram in doc_trigrams
    if q.op == "AND":
        return all(eval_trigram_query_on_doc(c, doc_trigrams) for c in q.children)
    if q.op == "OR":
        return any(eval_trigram_query_on_doc(c, doc_trigrams) for c in q.children)
    raise ValueError(q.op)


def run_probe_1() -> dict[str, object]:
    # 1. Deterministic 240-document synthetic multi-package repository
    docs: list[str] = []
    for idx in range(240):
        mod = f"pkg_{idx // 12:02d}/handler_{idx:03d}.go"
        if idx in (17, 89):
            fn = "parseConfig"
        elif idx in (42, 155):
            fn = "buildConfig"
        elif idx % 5 == 0:
            fn = "handleRequestConfig"
        else:
            fn = f"processItem{idx:03d}"
        body = (
            f"// File {mod}\npackage pkg_{idx // 12:02d}\n"
            f"func {fn}(id int, ctx Context) (ok bool, err error) {{\n"
            f"    if id < 0 {{ return false, ErrInvalid }}\n"
            f"    return true, nil\n}}\n"
        )
        docs.append(body)

    doc_tri_sets = [{d[i : i + 3] for i in range(len(d) - 2)} for d in docs]

    # Regex 1: `(parse|build)Config`
    re_concat = RegexNode(
        "CONCAT",
        subs=(
            RegexNode("ALT", subs=(RegexNode("LIT", "parse"), RegexNode("LIT", "build"))),
            RegexNode("LIT", "Config"),
        ),
    )
    py_re_concat = re.compile(r"(?:parse|build)Config")
    cox_concat = compile_cox_trigram(re_concat)
    zoekt_concat = compile_zoekt_matchtree_query(re_concat)

    true_matches_1 = {i for i, d in enumerate(docs) if py_re_concat.search(d)}
    cox_cands_1 = {i for i, ts in enumerate(doc_tri_sets) if eval_trigram_query_on_doc(cox_concat.match, ts)}
    zoekt_cands_1 = {i for i, ts in enumerate(doc_tri_sets) if eval_trigram_query_on_doc(zoekt_concat, ts)}
    assert true_matches_1 == {17, 42, 89, 155}
    assert true_matches_1.issubset(cox_cands_1)  # Zero false negatives!
    assert len(cox_cands_1) == 4  # Exact 4/240 via cross-boundary `eCo`/`dCo`!
    assert len(zoekt_cands_1) == 4  # `(parse|build)` has >=3-char arms so Zoekt keeps AND(OR(parse,build), Config)

    # Regex 2: `(pa|bu)Config` — 2-rune alternation arms!
    # Cox preserves suffix x prefix `aCo` | `uCo` -> 0/240 candidates, whereas
    # Zoekt `eval.go:687-690` collapses `(pa|bu)` to `bruteForceMatchTree` (`ANY`),
    # leaving only `Config` (`51/240` candidates)!
    re_short_alt = RegexNode(
        "CONCAT",
        subs=(
            RegexNode("ALT", subs=(RegexNode("LIT", "pa"), RegexNode("LIT", "bu"))),
            RegexNode("LIT", "Config"),
        ),
    )
    cox_short = compile_cox_trigram(re_short_alt)
    zoekt_short = compile_zoekt_matchtree_query(re_short_alt)
    cox_cands_2 = {i for i, ts in enumerate(doc_tri_sets) if eval_trigram_query_on_doc(cox_short.match, ts)}
    zoekt_cands_2 = {i for i, ts in enumerate(doc_tri_sets) if eval_trigram_query_on_doc(zoekt_short, ts)}
    true_matches_2 = {i for i, d in enumerate(docs) if re.search(r"(?:pa|bu)Config", d)}
    assert true_matches_2 == set() and len(cox_cands_2) == 0 and len(zoekt_cands_2) == 51
    assert true_matches_2.issubset(cox_cands_2)

    # Also test `(se|ld)Config`, which matches `{17, 42, 89, 155}` via `parseConfig` / `buildConfig`:
    re_seld = RegexNode(
        "CONCAT",
        subs=(
            RegexNode("ALT", subs=(RegexNode("LIT", "se"), RegexNode("LIT", "ld"))),
            RegexNode("LIT", "Config"),
        ),
    )
    cox_seld = compile_cox_trigram(re_seld)
    zoekt_seld = compile_zoekt_matchtree_query(re_seld)
    cox_cands_seld = {i for i, ts in enumerate(doc_tri_sets) if eval_trigram_query_on_doc(cox_seld.match, ts)}
    zoekt_cands_seld = {i for i, ts in enumerate(doc_tri_sets) if eval_trigram_query_on_doc(zoekt_seld, ts)}
    assert true_matches_1.issubset(cox_cands_seld)
    assert len(cox_cands_seld) == 4  # `seCo` | `ldCo` narrows to 4/240 (1.67%)!
    assert len(zoekt_cands_seld) == 51  # Zoekt drops `(se|ld)` and scans all 51 `*Config` files (12.75x)!

    # Bounded repetition `OpRepeat` (`eval.go:639-650`): `[01]{3}` & `(ab|cd){2}`
    # Cox preserves exact cross-products when `|exact| <= max_set = 8` (`2^3 = 8` on `[01]{3}`,
    # `2^2 = 4` on `(ab|cd){2}`), whereas Zoekt `OpRepeat` recurses on `r.Sub[0]` -> `ANY`!
    re_bin3 = RegexNode("REPEAT", subs=(RegexNode("CLASS", "01"),), min_rep=3, max_rep=3)
    cox_bin3 = compile_cox_trigram(re_bin3, max_set=8)
    zoekt_bin3 = compile_zoekt_matchtree_query(re_bin3)
    assert cox_bin3.match.op == "OR" and len(cox_bin3.match.children) == 8 and zoekt_bin3.op == "ANY"

    re_abcd2 = RegexNode(
        "REPEAT",
        subs=(RegexNode("ALT", subs=(RegexNode("LIT", "ab"), RegexNode("LIT", "cd"))),),
        min_rep=2,
        max_rep=2,
    )
    cox_abcd2 = compile_cox_trigram(re_abcd2, max_set=8)
    zoekt_abcd2 = compile_zoekt_matchtree_query(re_abcd2)
    assert cox_abcd2.match.op == "OR" and len(cox_abcd2.match.children) == 4 and zoekt_abcd2.op == "ANY"

    # Regex 3: `(parseConfig|id)` & `<3`-rune literal `"id"` (`matchtree.go:1334`, `eval.go:687-690`)
    re_id_alt = RegexNode("ALT", subs=(RegexNode("LIT", "parseConfig"), RegexNode("LIT", "id")))
    cox_id_alt = compile_cox_trigram(re_id_alt)
    zoekt_id_alt = compile_zoekt_matchtree_query(re_id_alt)
    zoekt_short_lit = compile_zoekt_matchtree_query(RegexNode("LIT", "id"))
    assert cox_id_alt.match.op == "ANY" and zoekt_id_alt.op == "ANY" and zoekt_short_lit.op == "ANY"

    # 2. Zoekt 63-bit UTF-8 rune packing & sparse `makeRuneOffsetMap` (`bits.go:171, 467`)
    ascii_corpus = ("abcdefghij" * 250)  # 2,500 pure-ASCII runes
    ascii_samples = [i for i in range(0, len(ascii_corpus), RUNE_OFFSET_FREQUENCY)]
    ascii_map = make_rune_offset_map(ascii_samples)
    assert len(ascii_map) == 0  # 0 bytes of offset table for pure ASCII!

    utf8_unit = "fn_αβ_漢字_🚀!"  # 11 runes: 6 ASCII (1B) + 2 Greek (2B) + 2 CJK (3B) + 1 Rocket (4B) = 20 bytes
    utf8_corpus = (utf8_unit * 228)[:2500]
    utf8_b = utf8_corpus.encode("utf-8")
    true_byte_offs: list[int] = []
    b_acc = 0
    for ch in utf8_corpus:
        true_byte_offs.append(b_acc)
        b_acc += len(ch.encode("utf-8"))
    sampled_utf8 = [true_byte_offs[i] for i in range(0, len(utf8_corpus), RUNE_OFFSET_FREQUENCY)]
    utf8_map = make_rune_offset_map(sampled_utf8)
    assert len(utf8_map) == 24  # Index 0 == expected 0 elided; 24 corrections * 8B = 192B
    recovered_errors = sum(
        1
        for r_idx in range(len(utf8_corpus))
        if lookup_rune_offset(utf8_map, utf8_b, r_idx) != true_byte_offs[r_idx]
    )
    assert recovered_errors == 0

    # 3. `generateCaseNgrams` (`bits.go:27`) vs. ASCII-only `LowerRegexp` (`query/regexp.go:26`)
    foo_variants = generate_case_ngrams(runes_to_ngram("f", "o", "o"))
    ksk_variants = generate_case_ngrams(runes_to_ngram("k", "s", "k"))
    iota_variants = generate_case_ngrams(runes_to_ngram("\u1fbe", "\u1fbe", "\u1fbe"))
    assert len(foo_variants) == 8  # 2^3
    assert len(ksk_variants) == 27  # 3^3: {'k','K','\u212a'} x {'s','S','\u017f'} x {'k','K','\u212a'}
    assert len(iota_variants) == 64  # 4^3: {'\u0345','\u0399','\u03b9','\u1fbe'}^3
    kelvin_lowered = zoekt_query_lower_regexp_literal("KSK")
    assert kelvin_lowered == "KsK"  # 'S' folded to 's', but U+212A Kelvin 'K' left unfolded!

    # 4. `findSelectiveNgrams` + `distanceHitIterator` (`indexdata.go:357`, `hititer.go:51`)
    postings: dict[int, list[int]] = {}
    rune_cursor = 0
    doc_end_runes: list[int] = []
    for d in docs:
        for i in range(len(d) - 2):
            ng = runes_to_ngram(d[i], d[i + 1], d[i + 2])
            postings.setdefault(ng, []).append(rune_cursor + i)
        rune_cursor += len(d)
        doc_end_runes.append(rune_cursor)
    posting_sizes = {ng: len(pl) for ng, pl in postings.items()}
    pat = "parseConfig"
    first_ng, last_ng = find_selective_ngrams(pat, posting_sizes)
    dist = last_ng[0] - first_ng[0]
    raw_hits = distance_hit_intersect(postings[first_ng[1]], postings[last_ng[1]], dist)
    hit_docs = {bisect.bisect_right(doc_end_runes, h) for h in raw_hits}
    assert hit_docs == {17, 89}

    # 5. `scoreFileBM25` (`score.go:263, 398`) Constant-IDF & Shard-Local `averageFileLength` Drift
    # (a) Constant-IDF inversion on 2-term query `err parseZigbeeFrame` across 240 docs:
    # Doc A has 12 occurrences of ubiquitous `err` (df=240) and 0 of `parseZigbeeFrame` (df=1).
    # Doc B has 1 occurrence of rare `parseZigbeeFrame` (df=1) and 0 of `err` (df=240), equal byte len.
    z_doc_a = zoekt_bm25_file_score({"err": 12, "parseZigbeeFrame": 0}, 1200, [1200] * 240)
    z_doc_b = zoekt_bm25_file_score({"err": 0, "parseZigbeeFrame": 1}, 1200, [1200] * 240)
    idf_err = math.log(1.0 + (240 - 240 + 0.5) / (240 + 0.5))
    idf_rare = math.log(1.0 + (240 - 1 + 0.5) / (1 + 0.5))
    true_bm25_a = idf_err * z_doc_a
    true_bm25_b = idf_rare * z_doc_b
    assert z_doc_a > z_doc_b and true_bm25_b > true_bm25_a

    # (b) Shard-local `averageFileLength` drift for the EXACT SAME 1,200-byte file (`tf=1` & `tf=3`)
    target_bytes = 1200
    shard_small_configs = [target_bytes] + [360] * 19  # mean = 402.0 B
    shard_large_protos = [target_bytes] + [12568] * 19  # mean = 11999.6 B
    score_in_small_shard = zoekt_bm25_file_score({"sym": 1}, target_bytes, shard_small_configs)
    score_in_large_shard = zoekt_bm25_file_score({"sym": 1}, target_bytes, shard_large_protos)
    drift_ratio = score_in_large_shard / score_in_small_shard
    drift_ratio_tf3 = (
        zoekt_bm25_file_score({"sym": 3}, target_bytes, shard_large_protos)
        / zoekt_bm25_file_score({"sym": 3}, target_bytes, shard_small_configs)
    )
    assert drift_ratio > 2.5 and drift_ratio_tf3 > 1.75

    print("[Probe 1] Russ Cox Trigram Planner & Zoekt Engine [Basis: source + execution]")
    print(
        f"  [deterministic synthetic repo, N=240 docs] Regex selectivity: '(parse|build)Config' Cox={len(cox_cands_1)}/240, "
        f"'(se|ld)Config' Cox={len(cox_cands_seld)}/240 vs Zoekt={len(zoekt_cands_seld)}/240 (12.75x), "
        f"'[01]{{3}}'/'(ab|cd){{2}}' Cox={len(cox_bin3.match.children)}/{len(cox_abcd2.match.children)}-arm OR vs Zoekt=ANY, "
        f"'id' & '(parseConfig|id)' Zoekt=240/240 (100.0% bruteForce)"
    )
    print(
        f"  Zoekt UTF-8 runeOffsetMap (freq=100, 2500 runes): ascii_bytes={len(ascii_map)*8}, "
        f"utf8_bytes={len(utf8_map)*8} (errors={recovered_errors}); "
        f"SimpleFold('foo'={len(foo_variants)}, 'ksk'={len(ksk_variants)} [3.375x], 'ιιι'={len(iota_variants)} [8x], LowerRegexp('KSK')='{kelvin_lowered}')"
    )
    print(
        f"  Zoekt scoreFileBM25 (`score.go:263,398`): const_IDF('err'*12={z_doc_a:.4f} > rare*1={z_doc_b:.4f} "
        f"vs Robertson_IDF {true_bm25_a:.4f} < {true_bm25_b:.4f}); "
        f"shard_local_drift(tf=1)={score_in_small_shard:.4f} vs {score_in_large_shard:.4f} ({drift_ratio:.3f}x, tf=3 {drift_ratio_tf3:.3f}x)"
    )
    return {
        "cox_seld": len(cox_cands_seld),
        "zoekt_seld": len(zoekt_cands_seld),
        "ksk_variants": len(ksk_variants),
        "iota_variants": len(iota_variants),
        "drift_ratio": drift_ratio,
    }


# ============================================================================
# PROBE 2: SCIP Protobuf Streaming vs. LSIF v0.5.0 Graph & PositionEncoding
# ============================================================================


def _encode_varint(val: int) -> bytes:
    assert val >= 0
    out = bytearray()
    while val > 0x7F:
        out.append((val & 0x7F) | 0x80)
        val >>= 7
    out.append(val)
    return bytes(out)


def _decode_varint(buf: bytes, pos: int) -> tuple[int, int]:
    shift = 0
    result = 0
    while True:
        b = buf[pos]
        pos += 1
        result |= (b & 0x7F) << shift
        if (b & 0x80) == 0:
            return result, pos
        shift += 7


def _pb_tag(field_num: int, wire_type: int) -> bytes:
    return _encode_varint((field_num << 3) | wire_type)


def _pb_bytes(field_num: int, payload: bytes) -> bytes:
    return _pb_tag(field_num, 2) + _encode_varint(len(payload)) + payload


def _pb_str(field_num: int, text: str) -> bytes:
    return _pb_bytes(field_num, text.encode("utf-8"))


def _pb_varint_field(field_num: int, val: int) -> bytes:
    return _pb_tag(field_num, 0) + _encode_varint(val)


def _pb_packed_int32(field_num: int, vals: tuple[int, ...]) -> bytes:
    body = b"".join(_encode_varint(v) for v in vals)
    return _pb_bytes(field_num, body)


def _decode_pb_fields(buf: bytes) -> list[tuple[int, int, int | bytes]]:
    """Minimal Protobuf wire-field decoder (`varint` wire_type=0, `LEN` wire_type=2)
    to validate `Metadata` (`1..4`) and `Document` (`1, 2, 3, 4, 6`) tags against
    `sourcegraph/scip@8fe50375` (`scip.proto:41-54, 76-120`).
    """
    pos = 0
    fields: list[tuple[int, int, int | bytes]] = []
    while pos < len(buf):
        tag, pos = _decode_varint(buf, pos)
        field_num = tag >> 3
        wire_type = tag & 0x07
        if wire_type == 0:
            val, pos = _decode_varint(buf, pos)
            fields.append((field_num, wire_type, val))
        elif wire_type == 2:
            ln, pos = _decode_varint(buf, pos)
            fields.append((field_num, wire_type, buf[pos : pos + ln]))
            pos += ln
        else:
            raise ValueError(f"Unsupported wire_type {wire_type} on field {field_num}")
    return fields


def encode_scip_occurrence(
    line: int,
    start_col: int,
    end_col: int,
    symbol: str,
    roles: int,
    range_mode: str = "packed",
) -> bytes:
    """Encodes `scip.Occurrence` (`scip.proto:694-746`) at `sourcegraph/scip@8fe50375`:
      - `packed`: `repeated int32 range = 1` `[line, start_col, end_col]`
      - `typed`: `SingleLineRange single_line_range = 8` (`line=1, start=2, end=3`)
      - `lsp_nested`: historical draft nested `Range{start: Pos, end: Pos}` (`scip.proto:701-705`)
    """
    out = bytearray()
    if range_mode == "packed":
        out += _pb_packed_int32(1, (line, start_col, end_col))
    elif range_mode == "typed":
        slr = (
            _pb_varint_field(1, line)
            + _pb_varint_field(2, start_col)
            + _pb_varint_field(3, end_col)
        )
        out += _pb_bytes(8, slr)
    elif range_mode == "lsp_nested":
        p_start = _pb_varint_field(1, line) + _pb_varint_field(2, start_col)
        p_end = _pb_varint_field(1, line) + _pb_varint_field(2, end_col)
        rng = _pb_bytes(1, p_start) + _pb_bytes(2, p_end)
        out += _pb_bytes(1, rng)
    else:
        raise ValueError(range_mode)
    out += _pb_str(2, symbol)
    if roles:
        out += _pb_varint_field(3, roles)
    return bytes(out)


def parse_scip_streaming(stream: io.BytesIO) -> tuple[int, int, int]:
    """Faithful port of `IndexVisitor.ParseStreaming` (`bindings/go/scip/parse.go:29-122`)
    at `sourcegraph/scip@8fe503757e133d98312b059b89e0ad5f72852d53`.
    Reads 1-byte LEN tags (`0x0a` metadata, `0x12` document, `0x1a` external_symbols),
    validates inner `Metadata` (`fields 1..4`) and `Document` (`position_encoding = 6`)
    wire schemas against `scip.proto`, and processes one `Document` message at a time
    in `O(max |D_i|)` RAM.
    """
    meta_count = 0
    doc_count = 0
    peak_doc_buf = 0
    while True:
        tag_b = stream.read(1)
        if not tag_b:
            break
        tag = tag_b[0]
        field_num = tag >> 3
        wire_type = tag & 0x07
        if wire_type != 2 or field_num not in (1, 2, 3):
            raise ValueError(f"Unexpected SCIP Index wire tag: 0x{tag:02x}")
        # Read varint message length (`readVarint`, `parse.go:134-156`)
        shift = 0
        msg_len = 0
        while True:
            b_arr = stream.read(1)
            if not b_arr:
                raise EOFError("Truncated varint in SCIP stream")
            b = b_arr[0]
            msg_len |= (b & 0x7F) << shift
            if (b & 0x80) == 0:
                break
            shift += 7
        payload = stream.read(msg_len)
        if len(payload) != msg_len:
            raise EOFError("Truncated sub-message in SCIP stream")
        peak_doc_buf = max(peak_doc_buf, len(payload))
        sub_fields = _decode_pb_fields(payload)
        if field_num == 1:
            meta_tags = {fn for fn, _, _ in sub_fields}
            assert meta_tags.issubset({1, 2, 3, 4}), f"Invalid Metadata field tags: {meta_tags}"
            assert (4, 0, 1) in sub_fields  # Metadata.text_document_encoding = UTF8 (1)
            meta_count += 1
        elif field_num == 2:
            doc_tags = {fn for fn, _, _ in sub_fields}
            assert doc_tags.issubset({1, 2, 3, 4, 5, 6}), f"Invalid Document field tags: {doc_tags}"
            assert (6, 0, 1) in sub_fields  # Document.position_encoding = UTF8CodeUnitOffsetFromLineStart (1)
            doc_count += 1
    return meta_count, doc_count, peak_doc_buf


def compute_scip_position_offsets(line: str, target_char_idx: int) -> tuple[int, int, int]:
    """Computes `scip.PositionEncoding` (`scip.proto:122-146`) offsets from line start:
      1 = UTF-8 code units (bytes)
      2 = UTF-16 code units (2-byte units; astral supplementary code points count as 2)
      3 = UTF-32 code units (Unicode scalar values / runes)
    """
    prefix = line[:target_char_idx]
    utf8_off = len(prefix.encode("utf-8"))
    utf16_off = len(prefix.encode("utf-16-le")) // 2
    utf32_off = len(prefix)
    return utf8_off, utf16_off, utf32_off


def slice_utf16_cols_correctly(line: str, utf16_start: int, utf16_end: int) -> str:
    raw16 = line.encode("utf-16-le")
    return raw16[utf16_start * 2 : utf16_end * 2].decode("utf-16-le")


def run_probe_2() -> dict[str, object]:
    # Deterministic 20-document, 100-symbol, 1,200-occurrence multi-package workspace
    num_docs = 20
    num_symbols = 100
    occs_per_doc = 60  # 20 * 60 = 1,200 total occurrences

    symbols = [
        f"scip-go gomod github.com/acme/monorepo v1.4.0 pkg_{s // 5:02d}/Service{s:03d}#Execute()."
        for s in range(num_symbols)
    ]

    # Build SCIP payloads (`packed` [field 1], `typed` [field 8], and `lsp_nested` draft)
    # Conformant with `sourcegraph/scip@8fe50375` (`scip.proto:41-54` `Metadata` & `76-120` `Document`):
    #   - `Metadata` field 4 = `TextEncoding.UTF8` (`1`) (`scip.proto:53`)
    #   - `Document` field 6 = `PositionEncoding.UTF8CodeUnitOffsetFromLineStart` (`1`) (`scip.proto:118`)
    def build_scip_index(range_mode: str) -> tuple[bytes, int]:
        meta = (
            _pb_varint_field(1, 0)
            + _pb_bytes(2, _pb_str(1, "scip-go") + _pb_str(2, "0.4.0"))
            + _pb_str(3, "file:///workspace")
            + _pb_varint_field(4, 1)  # Metadata.text_document_encoding = UTF8 (scip.proto:53)
        )
        stream_parts = [_pb_bytes(1, meta)]
        symbol_string_bytes = 0
        for d in range(num_docs):
            doc_body = bytearray()
            doc_body += _pb_str(4, "go")
            doc_body += _pb_str(1, f"internal/pkg_{d // 4:02d}/module_{d:02d}.go")
            doc_body += _pb_varint_field(6, 1)  # Document.position_encoding = UTF8CodeUnitOffsetFromLineStart (scip.proto:118)
            for k in range(occs_per_doc):
                sym_idx = (d * 5 + (k % 15)) % num_symbols
                sym_str = symbols[sym_idx]
                is_def = (k < 5) and (sym_idx // 5 == d)
                roles = 1 if is_def else 0
                line_no = 10 + k * 2
                col_start = 8
                col_end = 15
                occ_b = encode_scip_occurrence(
                    line_no, col_start, col_end, sym_str, roles, range_mode
                )
                doc_body += _pb_bytes(2, occ_b)
                symbol_string_bytes += len(sym_str.encode("utf-8"))
                if is_def:
                    sym_info = _pb_str(1, sym_str) + _pb_str(
                        3, f"Execute handles RPC request for Service{sym_idx:03d}."
                    )
                    doc_body += _pb_bytes(3, sym_info)
            stream_parts.append(_pb_bytes(2, bytes(doc_body)))
        return b"".join(stream_parts), symbol_string_bytes

    scip_packed, sym_str_bytes = build_scip_index("packed")
    scip_typed, _ = build_scip_index("typed")
    scip_lsp_nested, _ = build_scip_index("lsp_nested")

    # Build equivalent normative LSIF v0.5.0 JSON-Lines dump (`shard` on `item` edges)
    next_id = 0

    def alloc_id() -> int:
        nonlocal next_id
        next_id += 1
        return next_id

    lsif_lines: list[str] = []
    vertex_count = 0
    edge_count = 0

    def emit_v(label: str, **props: object) -> int:
        nonlocal vertex_count
        vid = alloc_id()
        vertex_count += 1
        obj = {"id": vid, "type": "vertex", "label": label, **props}
        lsif_lines.append(json.dumps(obj, separators=(",", ":")))
        return vid

    def emit_e(label: str, out_v: int, in_v: Optional[int] = None, **props: object) -> int:
        nonlocal edge_count
        eid = alloc_id()
        edge_count += 1
        obj: dict[str, object] = {"id": eid, "type": "edge", "label": label, "outV": out_v}
        if in_v is not None:
            obj["inV"] = in_v
        obj.update(props)
        lsif_lines.append(json.dumps(obj, separators=(",", ":")))
        return eid

    emit_v("metaData", version="0.5.0", projectRoot="file:///workspace", positionEncoding="utf-16")
    proj_id = emit_v("project", kind="go")

    # Pre-create resultSet + definitionResult + referenceResult + hoverResult + moniker per symbol
    sym_nodes: dict[int, tuple[int, int, int]] = {}
    for s_idx, sym_str in enumerate(symbols):
        rs_id = emit_v("resultSet")
        def_id = emit_v("definitionResult")
        ref_id = emit_v("referenceResult")
        hov_id = emit_v(
            "hoverResult",
            result={"contents": [{"language": "go", "value": f"Execute Service{s_idx:03d}"}]},
        )
        mon_id = emit_v("moniker", scheme="gomod", identifier=sym_str, unique="scheme", kind="export")
        emit_e("textDocument/definition", rs_id, def_id)
        emit_e("textDocument/references", rs_id, ref_id)
        emit_e("textDocument/hover", rs_id, hov_id)
        emit_e("moniker", rs_id, mon_id)
        sym_nodes[s_idx] = (rs_id, def_id, ref_id)

    doc_ids: list[int] = []
    for d in range(num_docs):
        doc_vid = emit_v(
            "document",
            uri=f"file:///workspace/internal/pkg_{d // 4:02d}/module_{d:02d}.go",
            languageId="go",
        )
        doc_ids.append(doc_vid)
        doc_ranges: list[int] = []
        for k in range(occs_per_doc):
            sym_idx = (d * 5 + (k % 15)) % num_symbols
            is_def = (k < 5) and (sym_idx // 5 == d)
            line_no = 10 + k * 2
            rng_id = emit_v(
                "range",
                start={"line": line_no, "character": 8},
                end={"line": line_no, "character": 15},
            )
            doc_ranges.append(rng_id)
            rs_id, def_id, ref_id = sym_nodes[sym_idx]
            emit_e("next", rng_id, rs_id)
            if is_def:
                emit_e("item", def_id, inVs=[rng_id], shard=doc_vid)
                emit_e("item", ref_id, inVs=[rng_id], shard=doc_vid, property="definitions")
            else:
                emit_e("item", ref_id, inVs=[rng_id], shard=doc_vid, property="references")
        emit_e("contains", doc_vid, inVs=doc_ranges)
    emit_e("contains", proj_id, inVs=doc_ids)

    lsif_raw = ("\n".join(lsif_lines) + "\n").encode("utf-8")
    scip_gz = gzip.compress(scip_packed, compresslevel=9, mtime=0)
    lsif_gz = gzip.compress(lsif_raw, compresslevel=9, mtime=0)

    meta_n, doc_n, peak_doc_bytes = parse_scip_streaming(io.BytesIO(scip_packed))
    assert meta_n == 1 and doc_n == num_docs

    raw_ratio = len(lsif_raw) / len(scip_packed)
    gz_ratio = len(lsif_gz) / len(scip_gz)
    typed_overhead_pct = 100.0 * (len(scip_typed) - len(scip_packed)) / len(scip_packed)
    packed_vs_nested_saving_pct = 100.0 * (len(scip_lsp_nested) - len(scip_packed)) / len(scip_lsp_nested)
    inline_sym_pct = 100.0 * sym_str_bytes / len(scip_packed)

    # Verify normative `scip.proto:129-145` `"🚀 Woo"` PositionEncoding offsets & slicing trap
    spec_example = "🚀 Woo"
    u8_w, u16_w, u32_w = compute_scip_position_offsets(spec_example, spec_example.index("W"))
    assert (u8_w, u16_w, u32_w) == (5, 3, 2)

    ts_line = 'const status = "🚀 ready"; return verifyToken(ctx);'
    id_char_start = ts_line.index("verifyToken")
    id_char_end = id_char_start + len("verifyToken")
    _, u16_s, _ = compute_scip_position_offsets(ts_line, id_char_start)
    _, u16_e, _ = compute_scip_position_offsets(ts_line, id_char_end)
    # Naive byte-slicing of UTF-8 source using LSP/TS UTF-16 column offsets shifts left by 2 bytes!
    naive_utf8_slice = ts_line.encode("utf-8")[u16_s:u16_e].decode("utf-8", errors="replace")
    exact_slice = slice_utf16_cols_correctly(ts_line, u16_s, u16_e)
    assert naive_utf8_slice == "n verifyTok" and exact_slice == "verifyToken"

    print("[Probe 2] SCIP Streaming Wire Protocol vs. LSIF v0.5.0 Graph [Basis: normative + source + execution]")
    print(
        f"  [deterministic synthetic workspace, 20 docs / 1200 occs] SCIP_packed={len(scip_packed)}B (gzip={len(scip_gz)}B) vs "
        f"LSIF_0.5.0={len(lsif_raw)}B (gzip={len(lsif_gz)}B) -> raw={raw_ratio:.2f}x, gzip={gz_ratio:.2f}x"
    )
    print(
        f"  Streaming state & range wire: SCIP_peak_doc_buf={peak_doc_bytes}B (docs={doc_n}) vs "
        f"LSIF_elements={vertex_count + edge_count} (V={vertex_count}, E={edge_count}); "
        f"packed_vs_LSP_Range=-{packed_vs_nested_saving_pct:.1f}%, typed_range=+{typed_overhead_pct:.2f}%, "
        f"inline_symbol_share={inline_sym_pct:.1f}%"
    )
    print(
        f"  PositionEncoding ('🚀 Woo' -> 'W'): UTF8={u8_w}, UTF16={u16_w}, UTF32={u32_w}; "
        f"naive_UTF16_on_UTF8='{naive_utf8_slice}' vs transcoded='{exact_slice}'"
    )
    return {
        "scip_packed_bytes": len(scip_packed),
        "scip_gz_bytes": len(scip_gz),
        "peak_doc_bytes": peak_doc_bytes,
        "raw_ratio": raw_ratio,
        "gz_ratio": gz_ratio,
        "lsif_elements": vertex_count + edge_count,
    }


# ============================================================================
# PROBE 3: cAST (`yilinjz/astchunk@82029ada`) & Live Benchmark Harness Defects
# ============================================================================


@dataclass
class MiniTSNode:
    """Statement-flattened CST/AST span node built from stdlib `ast` as a
    pure-Python surrogate for `tree-sitter-python` (matching Tree-sitter UTF-8
    byte offsets and 0-indexed `(row, byte_col)` coordinates).
    """

    node_type: str
    start_byte: int
    end_byte: int
    start_line: int
    start_col: int
    end_line: int
    end_col: int
    text_bytes: bytes
    children: list["MiniTSNode"]


@dataclass
class PortedASTNode:
    """Port of `astchunk.ASTNode` (`yilinjz/astchunk@82029ada`)."""

    ts_node: MiniTSNode
    size: int
    ancestors: tuple[MiniTSNode, ...] = ()

    @property
    def start_line(self) -> int:
        return self.ts_node.start_line

    @property
    def start_col(self) -> int:
        return self.ts_node.start_col

    @property
    def end_line(self) -> int:
        return self.ts_node.end_line

    @property
    def end_col(self) -> int:
        return self.ts_node.end_col

    @property
    def strcode(self) -> str:
        return self.ts_node.text_bytes.decode("utf-8")


def preprocess_nws_count_upstream(bstring: bytes) -> list[int]:
    """Exact port of `preprocess_nws_count` (`src/astchunk/preprocessing.py:84-94`):
    counts non-whitespace UTF-8 BYTES (`x not in whitespace_bytes`)!
    """
    ws_bytes = {ord(x) for x in string.whitespace}
    cumsum = [0]
    acc = 0
    for b in bstring:
        if b not in ws_bytes:
            acc += 1
        cumsum.append(acc)
    return cumsum


def get_nws_count_direct_upstream(code: str) -> int:
    """Exact port of `get_nws_count_direct` (`src/astchunk/preprocessing.py:105-111`):
    counts non-whitespace Unicode CHARACTERS (`code: str`)!
    """
    return sum(1 for ch in code if ch not in string.whitespace)


def rebuild_code_upstream(ast_window: list[PortedASTNode]) -> str:
    """Exact port of `ASTChunk.rebuild_code` (`src/astchunk/astchunk.py:64-102`).
    Reconstructs indentation via `" " * (node.start_col - current_col)` (`L82, 94`).
    """
    current_line, current_col = ast_window[0].start_line, ast_window[0].start_col
    code = " " * current_col
    for node in ast_window:
        if node.start_line > current_line:
            code += "\n" * (node.start_line - current_line)
            current_line = node.start_line
            current_col = 0
        if node.start_col > current_col:
            code += " " * (node.start_col - current_col)
            current_col = node.start_col
        code += node.strcode
        current_line, current_col = node.end_line, node.end_col
    return code


def build_chunk_ancestors_upstream(ancestors: tuple[MiniTSNode, ...]) -> list[str]:
    """Exact port of `ASTChunk.build_chunk_ancestors` (`src/astchunk/astchunk.py:104-130`):
    hardcodes Python-only `("class_definition", "function_definition")` (`L124-127`).
    """
    out: list[str] = []
    for node in ancestors:
        if node.node_type in ("class_definition", "function_definition"):
            out.append(node.text_bytes.decode("utf-8").split("\n")[0])
    return out


def apply_chunk_expansion_upstream(chunk_text: str, filepath: str, ancestors: list[str]) -> str:
    """Exact port of `ASTChunk.apply_chunk_expansion` (`src/astchunk/astchunk.py:173-195`)."""
    anc_str = "\n".join("\t" * i + a for i, a in enumerate(ancestors))
    hdr = "'''\n"
    if filepath:
        hdr += f"{filepath}\n"
    if anc_str:
        hdr += f"{anc_str}\n"
    hdr += "'''"
    return f"{hdr}\n{chunk_text}"


def _py_ast_to_mini_ts(source: str) -> MiniTSNode:
    """Builds a statement-flattened span hierarchy from stdlib `ast` with exact
    UTF-8 byte offsets and 0-based `(line, utf8_byte_col)` coordinates.
    Note: because `tree_sitter` is a C extension outside the Python standard
    library, compound `class`/`def` nodes emit a synthetic `"header"` signature
    child followed directly by suite statement children, whereas real
    `tree-sitter-python` emits concrete header token nodes (`def`, `identifier`,
    `parameters`, `:`) plus an intermediate `block` child wrapping the suite.
    """
    raw_lines = source.splitlines(keepends=True)
    line_byte_starts = [0]
    for ln in raw_lines:
        line_byte_starts.append(line_byte_starts[-1] + len(ln.encode("utf-8")))
    src_bytes = source.encode("utf-8")

    type_map = {
        ast.Module: "module",
        ast.ClassDef: "class_definition",
        ast.FunctionDef: "function_definition",
        ast.AsyncFunctionDef: "function_definition",
    }

    def to_byte_pos(lineno_1: int, char_col: int) -> tuple[int, int, int]:
        line_str = raw_lines[lineno_1 - 1]
        byte_col = len(line_str[:char_col].encode("utf-8"))
        return line_byte_starts[lineno_1 - 1] + byte_col, lineno_1 - 1, byte_col

    def convert_stmt_list(stmts: list[ast.stmt]) -> list[MiniTSNode]:
        out: list[MiniTSNode] = []
        for st in stmts:
            assert st.end_lineno is not None and st.end_col_offset is not None
            sb, sl, sc = to_byte_pos(st.lineno, st.col_offset)
            eb, el, ec = to_byte_pos(st.end_lineno, st.end_col_offset)
            ntype = type_map.get(type(st), type(st).__name__.lower())
            body_stmts = getattr(st, "body", None)
            children = convert_stmt_list(body_stmts) if isinstance(body_stmts, list) else []
            # If compound statement (`class`/`def`), include header signature pseudo-child
            # so splitting `class`/`def` preserves the `class Foo:` / `def bar():` header
            # (standing in for `tree-sitter-python` header tokens before `block`).
            if children:
                first_child_sb = children[0].start_byte
                hdr_end = first_child_sb
                while hdr_end > sb and src_bytes[hdr_end - 1 : hdr_end] in (b" ", b"\t", b"\n", b"\r"):
                    hdr_end -= 1
                if hdr_end > sb:
                    hdr_text = src_bytes[sb:hdr_end].decode("utf-8")
                    hdr_lines = hdr_text.split("\n")
                    hdr_el = sl + len(hdr_lines) - 1
                    hdr_ec = (
                        sc + len(hdr_lines[0].encode("utf-8"))
                        if len(hdr_lines) == 1
                        else len(hdr_lines[-1].encode("utf-8"))
                    )
                    hdr_node = MiniTSNode(
                        "header", sb, hdr_end, sl, sc, hdr_el, hdr_ec, src_bytes[sb:hdr_end], []
                    )
                    children = [hdr_node] + children
            out.append(MiniTSNode(ntype, sb, eb, sl, sc, el, ec, src_bytes[sb:eb], children))
        return out

    mod = ast.parse(source)
    children = convert_stmt_list(mod.body)
    end_line = max(0, len(raw_lines) - 1)
    end_col = len(raw_lines[-1].encode("utf-8")) if raw_lines else 0
    return MiniTSNode("module", 0, len(src_bytes), 0, 0, end_line, end_col, src_bytes, children)


def chunk_astchunk_upstream(
    source: str,
    max_chunk_size: int,
    merge_siblings: bool = True,
    chunk_overlap: int = 0,
    paper_alg1_bug: bool = False,
) -> list[tuple[list[PortedASTNode], str, int]]:
    """Exact algorithmic port of `ASTChunkBuilder` (`src/astchunk/astchunk_builder.py:46-226`)
    at `yilinjz/astchunk@82029ada8a8dd8d668283c076980cedb886e6d4c` over `_py_ast_to_mini_ts`.
    Note: upstream `astchunk_builder.py:72, 122` stores `ancestors` as a `pyrsistent.v`
    persistent vector so `ancestors.append(node)` returns a new `pvector` (passing a plain
    Python `list` directly to `assign_nodes_to_windows` crashes with `TypeError` because
    `list.append` returns `None`); here immutable `tuple` concatenation `ancestors + (node,)`
    models `pvector.append` in stdlib Python.
    When `paper_alg1_bug=True`, reproduces `arXiv:2506.15655v2` Algorithm 1 lines 16-29
    (which omits the `else:` branch at `astchunk_builder.py:127-130`).
    """
    root = _py_ast_to_mini_ts(source)
    nws_cumsum = preprocess_nws_count_upstream(source.encode("utf-8"))

    def nws_range(sb: int, eb: int) -> int:
        return nws_cumsum[eb] - nws_cumsum[sb]

    def merge_windows(wins: list[list[PortedASTNode]]) -> list[list[PortedASTNode]]:
        if not wins:
            return []
        merged: list[list[PortedASTNode]] = [list(wins[0])]
        for w in wins[1:]:
            # Exact `astchunk_builder.py:165`: sums `n.size` (UTF-8 non-WS bytes)
            cand_size = sum(n.size for n in merged[-1]) + sum(n.size for n in w)
            if cand_size <= max_chunk_size:
                merged[-1] = merged[-1] + w
            else:
                merged.append(list(w))
        return merged

    def assign_nodes(
        nodes: list[MiniTSNode], ancestors: tuple[MiniTSNode, ...]
    ) -> list[list[PortedASTNode]]:
        if not nodes:
            return []
        out_wins: list[list[PortedASTNode]] = []
        cur_win: list[PortedASTNode] = []
        cur_size = 0
        for node in nodes:
            node_size = nws_range(node.start_byte, node.end_byte)
            exceeds = node_size > max_chunk_size
            if (len(cur_win) == 0 and exceeds) or (cur_size + node_size > max_chunk_size):
                if cur_win:
                    out_wins.append(cur_win)
                    cur_win = []
                    cur_size = 0
                if exceeds:
                    child_wins = assign_nodes(node.children, ancestors + (node,))
                    if child_wins:
                        out_wins.extend(
                            merge_windows(child_wins) if merge_siblings else child_wins
                        )
                elif not paper_alg1_bug:
                    # `astchunk_builder.py:127-130` (missing in paper Algorithm 1!)
                    cur_win.append(PortedASTNode(node, node_size, ancestors))
                    cur_size += node_size
                    if not merge_siblings:
                        out_wins.append(cur_win)
                        cur_win, cur_size = [], 0
            else:
                cur_win.append(PortedASTNode(node, node_size, ancestors))
                cur_size += node_size
                if not merge_siblings:
                    out_wins.append(cur_win)
                    cur_win, cur_size = [], 0
        if cur_win:
            out_wins.append(cur_win)
        return out_wins

    tree_size = nws_range(root.start_byte, root.end_byte)
    if tree_size <= max_chunk_size:
        windows = [[PortedASTNode(root, tree_size, ())]]
    else:
        raw_wins = assign_nodes(root.children, (root,))
        windows = merge_windows(raw_wins) if merge_siblings else raw_wins

    if chunk_overlap > 0:
        overlapped: list[list[PortedASTNode]] = []
        for i, w in enumerate(windows):
            cur = list(w)
            if i > 0:
                prev = windows[i - 1]
                cur = prev[-min(chunk_overlap, len(prev)) :] + cur
            if i < len(windows) - 1:
                nxt = windows[i + 1]
                cur = cur + nxt[: min(chunk_overlap, len(nxt))]
            overlapped.append(cur)
        windows = overlapped

    results: list[tuple[list[PortedASTNode], str, int]] = []
    for w in windows:
        txt = rebuild_code_upstream(w)
        results.append((w, txt, get_nws_count_direct_upstream(txt)))
    return results


# --- Exact benchmark harness ports (`repobench@e0cfd34c` & `code-rag-bench@f9e100ca`) ---


def repobench_get_first_line_not_comment(code: str, language: str = "python") -> str:
    """Exact port of `get_first_line_not_comment` (`run.py:12-79`)
    at `Leolty/repobench@e0cfd34c9e7cd8f057efd32b9280b9719ae12a91`.
    """
    code = code.lstrip("\n")
    lines = code.split("\n")
    in_multiline_comment = False
    if language == "python":
        for line in lines:
            if not line.strip():
                continue
            if not in_multiline_comment and (
                line.strip().startswith('"""') or line.strip().startswith("'''")
            ):
                in_multiline_comment = True
                continue
            if in_multiline_comment and (
                line.strip().endswith('"""') or line.strip().endswith("'''")
            ):
                in_multiline_comment = False
                continue
            if in_multiline_comment:
                continue
            if line.strip().startswith("#"):
                continue
            return line
    elif language == "java":
        for line in lines:
            if not line.strip():
                continue
            if not in_multiline_comment and line.strip().startswith("/*"):
                in_multiline_comment = True
                continue
            if in_multiline_comment and line.strip().endswith("*/"):
                in_multiline_comment = False
                continue
            if in_multiline_comment:
                continue
            if line.strip().startswith("//"):
                continue
            return line
    return lines[0]


def coderag_get_chunks(text: str, num_tokens: int) -> list[str]:
    """Exact port of `get_chunks` (`generation/chunk.py:10-33`)
    at `code-rag-bench/code-rag-bench@f9e100ca9ed94b8f1983b356ae81966e30210cf4`
    using deterministic whitespace/punctuation subtokens.
    """
    tok_re = re.compile(r"\w+|[^\w\s]", re.UNICODE)
    line_tokens = [tok_re.findall(line) for line in text.split("\n")]
    raw_lines = text.split("\n")
    token_chunks: list[list[int]] = []
    curr_tokens = 0
    curr_chunk: list[int] = []
    for line_idx, lt in enumerate(line_tokens):
        if len(lt) + curr_tokens > num_tokens:
            token_chunks.append(curr_chunk)
            curr_tokens, curr_chunk = 0, []
            # Upstream BUG (`chunk.py:18-20`): `lt` is NEVER appended here!
        else:
            curr_chunk.append(line_idx)
            curr_tokens += len(lt)
    if curr_tokens > 0:
        token_chunks.append(curr_chunk)
    return ["\n".join(raw_lines[idx] for idx in ck) for ck in token_chunks]


def cosqa_plus_mmrr(relevant_ranks_1based: list[int]) -> float:
    """Exact formula for `MMRR` (`arXiv:2406.11589v1` §4.3):
    `m_i = (1/k) * sum_{j=1..k} 1 / (r_{i,j} - (j - 1))`.
    """
    ranks = sorted(relevant_ranks_1based)
    k = len(ranks)
    return sum(1.0 / (r - (j - 1)) for j, r in enumerate(ranks, start=1)) / k


def run_probe_3() -> dict[str, object]:
    # 1. Syntactic integrity: Fixed-Line vs. cAST Split-Only vs. Split-then-Merge
    methods_src = "\n\n".join(
        f"    def compute_stage_{i}(self, x: int, scale: int) -> int:\n"
        f"        base = (x * {i + 3}) + scale\n"
        f"        clamped = max(0, min(base, 10000))\n"
        f"        return clamped ^ {i * 7 + 1}"
        for i in range(8)
    )
    py_module = (
        "import math\nimport os\nimport sys\n\n"
        "class PipelineProcessor:\n"
        f"{methods_src}\n"
    )
    budget = 200  # 1.8x method size: fixed-line slices mid-function; cAST keeps methods whole!

    # Fixed-line chunking under the same 200 non-WS budget
    lines = py_module.splitlines()
    fixed_chunks: list[tuple[int, int]] = []
    c_start, c_nws = 1, 0
    for idx, ln in enumerate(lines, start=1):
        ln_nws = get_nws_count_direct_upstream(ln)
        if c_nws + ln_nws > budget and idx > c_start:
            fixed_chunks.append((c_start, idx - 1))
            c_start, c_nws = idx, ln_nws
        else:
            c_nws += ln_nws
    fixed_chunks.append((c_start, len(lines)))

    tree = ast.parse(py_module)
    fn_spans = [
        (n.lineno, n.end_lineno)
        for n in ast.walk(tree)
        if isinstance(n, ast.FunctionDef) and n.end_lineno is not None
    ]

    def count_broken_functions(chunk_line_spans: list[tuple[int, int]]) -> int:
        broken = 0
        for fs, fe in fn_spans:
            if not any(cs <= fs and fe <= ce for cs, ce in chunk_line_spans):
                broken += 1
        return broken

    fixed_broken = count_broken_functions(fixed_chunks)
    cast_merged = chunk_astchunk_upstream(py_module, budget, merge_siblings=True)
    cast_split_only = chunk_astchunk_upstream(py_module, budget, merge_siblings=False)
    cast_alg1_bug = chunk_astchunk_upstream(py_module, budget, merge_siblings=True, paper_alg1_bug=True)

    merged_spans = [(w[0].start_line + 1, w[-1].end_line + 1) for w, _, _ in cast_merged]
    cast_broken = count_broken_functions(merged_spans)
    assert fixed_broken > 0 and cast_broken == 0
    assert len(cast_split_only) > len(cast_merged)
    # Paper Algorithm 1 missing `else:` drops non-oversized siblings that trigger flush!
    alg1_kept_chars = sum(sz for _, _, sz in cast_alg1_bug)
    merged_kept_chars = sum(sz for _, _, sz in cast_merged)
    assert alg1_kept_chars < merged_kept_chars

    # 2. Five live `astchunk` source defects (`yilinjz/astchunk@82029ada`)
    # Bug A1: UTF-8 multi-byte CJK/emoji byte-vs-char mismatch (`preprocessing.py:90` vs `111`)
    cjk_src = 'MSG_A = "中文说明测试验证"\nMSG_B = "数据结构边界条件"\n'
    b_nws = preprocess_nws_count_upstream(cjk_src.encode("utf-8"))[-1]
    c_nws_true = get_nws_count_direct_upstream(cjk_src)
    cjk_chunks = chunk_astchunk_upstream(cjk_src, max_chunk_size=50)  # c_nws_true=32 <= 50, b_nws=64 > 50!
    assert c_nws_true <= 50 < b_nws and len(cjk_chunks) == 2

    # Bug A2: `\t -> " "` corruption in `rebuild_code` (`astchunk.py:82, 94`)
    # Sibling statements lose 100% of leading `\t`, while compound statements mix `" "` and `\t\t`!
    tab_src = "def calc(x):\n\ta = x + 1000\n\tb = a * 2000\n\treturn b\n"
    _, rebuilt_tab, _ = chunk_astchunk_upstream(tab_src, max_chunk_size=22)[1]
    assert "\t" not in rebuilt_tab and rebuilt_tab.startswith(" ") and not rebuilt_tab.startswith("    ")
    compound_tab_src = "def calc2(x):\n\tif x > 0:\n\t\treturn x + 1000\n\treturn 0\n"
    _, rebuilt_compound_tab, _ = chunk_astchunk_upstream(compound_tab_src, max_chunk_size=25)[1]
    assert rebuilt_compound_tab.startswith(" if ") and "\n\t\treturn" in rebuilt_compound_tab

    # Bug A3: Python-only `build_chunk_ancestors` (`astchunk.py:124-127`) & `filepath` cache bust
    ts_java_ancestors = (
        MiniTSNode("class_declaration", 0, 50, 0, 0, 5, 1, b"public class AuthService {", []),
        MiniTSNode("method_declaration", 10, 48, 1, 4, 4, 5, b"public boolean login() {", []),
    )
    assert build_chunk_ancestors_upstream(ts_java_ancestors) == []
    exp_old = apply_chunk_expansion_upstream("def f(): return 1", "src/old_name.py", [])
    exp_new = apply_chunk_expansion_upstream("def f(): return 1", "src/new_name.py", [])
    assert hashlib.sha256(exp_old.encode()).hexdigest() != hashlib.sha256(exp_new.encode()).hexdigest()

    # Bug A4: Silent deletion of oversized atomic leaf AST node (`astchunk_builder.py:121-126`)
    oversized_leaf_src = 'BIG_TABLE = "' + ("A" * 180) + '"\n'
    leaf_chunks = chunk_astchunk_upstream(oversized_leaf_src, max_chunk_size=100)
    assert len(leaf_chunks) == 0  # 100% of file silently dropped!

    # Bug A5: `add_window_overlapping` overflows `max_chunk_size` (`astchunk_builder.py:208-224`)
    ov_chunks = chunk_astchunk_upstream(py_module, max_chunk_size=115, chunk_overlap=1)
    max_ov_size = max(sz for _, _, sz in ov_chunks)
    assert max_ov_size > 115 * 2

    # 3. Live Benchmark Harness Defects (`repobench`, `code-rag-bench`, `CoSQA+`)
    rb_py_pred = '    """Validate incoming payload."""\n    return schema.check(payload)'
    rb_java_pred = "    /* Validate incoming payload */\n    return schema.check(payload);"
    rb_extracted_py = repobench_get_first_line_not_comment(rb_py_pred, "python")
    rb_extracted_java = repobench_get_first_line_not_comment(rb_java_pred, "java")
    assert rb_extracted_py.strip().startswith('"""') and rb_extracted_java.strip().startswith("/*")
    # `metrics.py:24` `pred.split() == gt.split()` accepts wrong Python block indentation!
    assert ("        return x".split() == "    return x".split()) is True
    assert ("return a+b".split() == "return a + b".split()) is False

    # `code-rag-bench` `chunk.py:17-25, 73` boundary-line deletion & empty first chunk
    sample_doc = (
        "def very_long_signature_exceeding_ten_subtokens(alpha: int, beta: int, gamma: int) -> int:\n"
        "    return alpha + beta + gamma\n"
    )
    crb_chunks = coderag_get_chunks(sample_doc, num_tokens=10)
    assert crb_chunks[0] == ""  # `truncate_text(...)[0]` returns empty string `""`!
    assert "very_long_signature" not in "\n".join(crb_chunks)  # Line 0 permanently deleted!

    # `code-rag-bench` `eval_beir_okapibm25.py:76` `doc.split(" ")` vs. subtokenization
    code_snippet = "def compute_checksum(payload_bytes):\n    return zlib.crc32(payload_bytes)"
    space_tokens = set(code_snippet.split(" "))
    sub_tokens = {part.lower() for tok in re.findall(r"[A-Za-z0-9]+", code_snippet) for part in tok.split("_")}
    assert "compute_checksum" not in space_tokens and "zlib" not in space_tokens
    assert {"compute", "checksum", "zlib", "payload"}.issubset(sub_tokens)

    # `CoSQA` single-target `MRR` crowding vs. `CoSQA+ v1` `MMRR`
    # Suppose 4 functionally valid implementations exist in corpus and rank at [1, 2, 3, 4],
    # while CoSQA's 1-to-1 pairing only annotated the 4th one:
    cosqa_1to1_mrr = 1.0 / 4.0
    cosqa_plus_mmrr_score = cosqa_plus_mmrr([1, 2, 3, 4])
    assert cosqa_1to1_mrr == 0.25 and cosqa_plus_mmrr_score == 1.0

    print("[Probe 3] cAST (`astchunk`) Syntactic Integrity & Live Harness Bugs [Basis: source + execution]")
    print(
        f"  8-method class chunking (budget={budget}): fixed_broken={fixed_broken}/8 vs cAST_broken={cast_broken}/8; "
        f"chunks(merged={len(cast_merged)}, split_only={len(cast_split_only)}); "
        f"Alg1_missing_else_chars={alg1_kept_chars}/{merged_kept_chars}"
    )
    print(
        f"  astchunk bugs: UTF8_CJK(chars={c_nws_true}, bytes={b_nws} -> chunks={len(cjk_chunks)}), "
        f"tab_preserved={'\\t' in rebuilt_tab}, java_ancestors={len(build_chunk_ancestors_upstream(ts_java_ancestors))}, "
        f"oversized_leaf_chunks={len(leaf_chunks)}, overlap1_max={max_ov_size} (>115)"
    )
    print(
        f"  Harness bugs: RepoBench_1line_docstring->'{rb_extracted_py.strip()}', "
        f"CodeRAG_truncate_long_line0='{crb_chunks[0]}' (line0_dropped=True), "
        f"BM25_space_has_zlib={'zlib' in space_tokens} (subtok=True), CoSQA_MRR={cosqa_1to1_mrr:.2f} vs MMRR={cosqa_plus_mmrr_score:.2f}"
    )
    return {
        "fixed_broken": fixed_broken,
        "cast_broken": cast_broken,
        "max_ov_size": max_ov_size,
    }


# ============================================================================
# PROBE 4: Hybrid Retrieval Fusion (Bruch TOIS 2023/2024 & Cormack SIGIR 2009)
# ============================================================================


def rank_desc(scores: list[float]) -> list[int]:
    """Returns 0-based document indices sorted by descending score (deterministic tie-break)."""
    return [idx for idx, _ in sorted(enumerate(scores), key=lambda x: (-x[1], x[0]))]


def rrf_fuse(sem_scores: list[float], lex_scores: list[float], k: int = 60) -> list[float]:
    """Cormack, Clarke, & Büttcher (SIGIR 2009): `sum 1 / (k + r(d))` (`1`-based ranks)."""
    n = len(sem_scores)
    sem_order = rank_desc(sem_scores)
    lex_order = rank_desc(lex_scores)
    r_sem = [0] * n
    r_lex = [0] * n
    for pos, doc_id in enumerate(sem_order, start=1):
        r_sem[doc_id] = pos
    for pos, doc_id in enumerate(lex_order, start=1):
        r_lex[doc_id] = pos
    return [1.0 / (k + r_sem[d]) + 1.0 / (k + r_lex[d]) for d in range(n)]


def m2c2_fuse(sem_scores: list[float], lex_scores: list[float], alpha: float) -> list[float]:
    """Empirical Min-Max Convex Combination (`M2C2`, Bruch et al. Eq. 2 & 3)."""

    def norm_mm(xs: list[float]) -> list[float]:
        lo, hi = min(xs), max(xs)
        if hi - lo == 0.0:
            return [0.0 for _ in xs]
        return [(x - lo) / (hi - lo) for x in xs]

    ns, nl = norm_mm(sem_scores), norm_mm(lex_scores)
    return [alpha * s + (1.0 - alpha) * l for s, l in zip(ns, nl)]


def tm2c2_fuse(sem_scores: list[float], lex_scores: list[float], alpha: float) -> list[float]:
    """Theoretical Min-Max Convex Combination (`TM2C2`, Bruch et al. Eq. 4):
    `phi_tmm(f_o(q, d)) = (f_o(q, d) - inf f_o) / (M_q - inf f_o)`,
    with `inf BM25 = 0.0` and `inf cosine = -1.0`.
    """
    m_sem = max(sem_scores)
    m_lex = max(lex_scores)
    ns = [(s - (-1.0)) / (m_sem - (-1.0)) if m_sem > -1.0 else 0.0 for s in sem_scores]
    nl = [(l - 0.0) / (m_lex - 0.0) if m_lex > 0.0 else 0.0 for l in lex_scores]
    return [alpha * s + (1.0 - alpha) * l for s, l in zip(ns, nl)]


def zscore_fuse(sem_scores: list[float], lex_scores: list[float], alpha: float) -> list[float]:
    """Z-Score Convex Combination (`Bruch et al.` Eq. 5)."""

    def norm_z(xs: list[float]) -> list[float]:
        mu = sum(xs) / len(xs)
        var = sum((x - mu) ** 2 for x in xs) / len(xs)
        sd = math.sqrt(var)
        if sd == 0.0:
            return [0.0 for _ in xs]
        return [(x - mu) / sd for x in xs]

    ns, nl = norm_z(sem_scores), norm_z(lex_scores)
    return [alpha * s + (1.0 - alpha) * l for s, l in zip(ns, nl)]


def ndcg_at_10(order: list[int], gold_doc: int) -> float:
    for rank_idx, d in enumerate(order[:10], start=1):
        if d == gold_doc:
            return 1.0 / math.log2(rank_idx + 1.0)
    return 0.0


def run_probe_4() -> dict[str, object]:
    # 1. Exact verification of Bruch et al. Lemma 4.2 single-query affine rank-equivalence
    sem_q = [0.62 + 0.005 * ((i * 17 + 3) % 50) for i in range(50)]
    lex_q = [1.5 + 0.37 * ((i * 29 + 11) % 50) for i in range(50)]
    alpha_mm = 0.72

    r_sem = max(sem_q) - min(sem_q)
    r_lex = max(lex_q) - min(lex_q)
    mu_s = sum(sem_q) / len(sem_q)
    mu_l = sum(lex_q) / len(lex_q)
    sd_s = math.sqrt(sum((x - mu_s) ** 2 for x in sem_q) / len(sem_q))
    sd_l = math.sqrt(sum((x - mu_l) ** 2 for x in lex_q) / len(lex_q))

    # Exact Lemma 4.2 weight mapping (`M2C2(alpha)` -> `Z-Score(alpha_z)` & `TM2C2(alpha_tmm)`)
    w_s_z = alpha_mm / (r_sem * sd_l)
    w_l_z = (1.0 - alpha_mm) / (r_lex * sd_s)
    alpha_z = w_s_z / (w_s_z + w_l_z)

    t_sem = max(sem_q) - (-1.0)
    t_lex = max(lex_q) - 0.0
    w_s_tmm = (alpha_mm / r_sem) * t_sem
    w_l_tmm = ((1.0 - alpha_mm) / r_lex) * t_lex
    alpha_tmm = w_s_tmm / (w_s_tmm + w_l_tmm)

    ord_mm = rank_desc(m2c2_fuse(sem_q, lex_q, alpha_mm))
    ord_z = rank_desc(zscore_fuse(sem_q, lex_q, alpha_z))
    ord_tmm = rank_desc(tm2c2_fuse(sem_q, lex_q, alpha_tmm))
    assert ord_mm == ord_z == ord_tmm

    # 2. `[illustrative analytical model]` (`Basis: derived`) across 3 regimes (48 queries, N=20 docs)
    # Fixed global `alpha = 0.80` (Bruch et al. §4.2 / Table 2 validation-tuned setting;
    # domain-knowledge operating interval `alpha in [0.6, 0.8]` in §7)
    alpha_global = 0.80
    regimes: dict[str, dict[str, list[float]]] = {
        "exact_symbol": {"rrf": [], "m2c2": [], "z": [], "tm2c2": []},
        "narrow_noise_nl": {"rrf": [], "m2c2": [], "z": [], "tm2c2": []},
        "boilerplate_outlier": {"rrf": [], "m2c2": [], "z": [], "tm2c2": []},
    }

    for q_idx in range(16):
        # Regime A: Exact rare-identifier query (`gold=0` has dominant BM25=38..44, rank #4 in dense;
        # `doc=1` has top dense cosine=0.838 & weak partial BM25=5.4, rank #2 in lexical!)
        # Notice RRF(60) gives doc=1 `1/61 + 1/62` > gold=0 `1/64 + 1/61`, losing the ~7x BM25 margin!
        sem_a = [0.790 - 0.008 * d for d in range(20)]
        sem_a[0] = 0.812  # dense rank #4
        sem_a[1] = 0.838  # dense rank #1
        sem_a[2] = 0.826  # dense rank #2
        sem_a[3] = 0.819  # dense rank #3
        lex_a = [max(0.0, 3.8 - 0.25 * d) for d in range(20)]
        lex_a[0] = 38.0 + 0.4 * q_idx  # true symbol definition (`~7x` runner-up!)
        lex_a[1] = 5.4  # lexical rank #2

        for key, fn in [
            ("rrf", lambda s, l: rrf_fuse(s, l, 60)),
            ("m2c2", lambda s, l: m2c2_fuse(s, l, alpha_global)),
            ("z", lambda s, l: zscore_fuse(s, l, alpha_global)),
            ("tm2c2", lambda s, l: tm2c2_fuse(s, l, alpha_global)),
        ]:
            regimes["exact_symbol"][key].append(ndcg_at_10(rank_desc(fn(sem_a, lex_a)), 0))

        # Regime B: NL conceptual query with tight positive BM25 stopword band (`m_q=4.00..4.06`)
        # `gold=0` is clear dense winner (`0.842` vs `0.810..0.813`), while `doc=1..5` have tiny +0.06 BM25 jitter!
        # `M2C2` and `Z-Score` stretch the 0.06 BM25 noise band across `[0, 1]` / `[-1.5, +2.6]`,
        # letting `1 - alpha = 0.20` lexical noise overtake the true `+0.03` cosine lead!
        # `TM2C2` anchors BM25 infimum at `0`, compressing `[4.00, 4.06]` to `[0.985, 1.000]`!
        sem_b = [0.790 - 0.004 * d for d in range(20)]
        sem_b[0] = 0.842  # gold semantic match
        sem_b[1] = 0.810 + 0.001 * (q_idx % 4)
        lex_b = [4.01 + 0.002 * (d % 5) for d in range(20)]
        lex_b[0] = 4.00  # lowest in tight noise band `[4.00, 4.06]`
        lex_b[1] = 4.06  # noisy stopword winner

        for key, fn in [
            ("rrf", lambda s, l: rrf_fuse(s, l, 60)),
            ("m2c2", lambda s, l: m2c2_fuse(s, l, alpha_global)),
            ("z", lambda s, l: zscore_fuse(s, l, alpha_global)),
            ("tm2c2", lambda s, l: tm2c2_fuse(s, l, alpha_global)),
        ]:
            regimes["narrow_noise_nl"][key].append(ndcg_at_10(rank_desc(fn(sem_b, lex_b)), 0))

        # Regime C: Spurious generated/mock file upper BM25 outlier (`M_q = 65.0 >> s_gold = 11.0`)
        # `doc=2` is an auto-generated mock repeating the symbol 90x (`BM25=65.0`, low cosine `0.61`).
        # `gold=0` has strong BM25 (`11.0`, rank #2) AND strong cosine (`0.818`, rank #2 behind `doc=1` `0.834` w/ `BM25=0.4`).
        # Because BOTH `M2C2` and `TM2C2` divide by `M_q = 65.0`, `gold`'s lexical score is crushed to `11/65 = 0.169`,
        # whereas `RRF(60)` ignores `65.0`'s magnitude (`rank #2` + `rank #2` beats `rank #1` + `rank #19` and `rank #20` + `rank #1`)!
        sem_c = [0.740 - 0.006 * d for d in range(20)]
        sem_c[0] = 0.818  # gold: rank #2 dense, rank #2 lexical
        sem_c[1] = 0.834  # distractor: rank #1 dense, near-zero lexical
        sem_c[2] = 0.610  # generated file outlier: rank #20 dense
        lex_c = [max(0.0, 2.5 - 0.15 * d) for d in range(20)]
        lex_c[2] = 65.0 + 0.5 * q_idx  # spurious boilerplate spike `M_q`!
        lex_c[0] = 11.0  # legitimate #2 lexical match
        lex_c[1] = 0.4

        for key, fn in [
            ("rrf", lambda s, l: rrf_fuse(s, l, 60)),
            ("m2c2", lambda s, l: m2c2_fuse(s, l, alpha_global)),
            ("z", lambda s, l: zscore_fuse(s, l, alpha_global)),
            ("tm2c2", lambda s, l: tm2c2_fuse(s, l, alpha_global)),
        ]:
            regimes["boilerplate_outlier"][key].append(ndcg_at_10(rank_desc(fn(sem_c, lex_c)), 0))

    means = {
        reg: {m: sum(vals) / len(vals) for m, vals in mdict.items()}
        for reg, mdict in regimes.items()
    }
    overall = {
        m: sum(means[reg][m] for reg in regimes) / 3.0
        for m in ("rrf", "m2c2", "z", "tm2c2")
    }
    assert means["exact_symbol"]["tm2c2"] > means["exact_symbol"]["rrf"]
    assert means["narrow_noise_nl"]["tm2c2"] > means["narrow_noise_nl"]["m2c2"]
    assert means["narrow_noise_nl"]["tm2c2"] > means["narrow_noise_nl"]["z"]
    assert means["boilerplate_outlier"]["rrf"] > means["boilerplate_outlier"]["tm2c2"]

    # Non-Lipschitz step jump in RRF under `2e-7` perturbation (`Bruch et al.` §5.2 Lipschitz continuity analysis)
    s_pert_1 = [0.8000000, 0.8000001, 0.7999999]
    s_pert_2 = [0.8000002, 0.8000001, 0.7999999]  # +2e-7 on doc 0 jumps rank 2 -> 1!
    l_pert = [5.0, 10.0, 20.0]
    rrf_delta = abs(rrf_fuse(s_pert_2, l_pert, 60)[0] - rrf_fuse(s_pert_1, l_pert, 60)[0])
    tm2c2_delta = abs(tm2c2_fuse(s_pert_2, l_pert, 0.8)[0] - tm2c2_fuse(s_pert_1, l_pert, 0.8)[0])
    lip_ratio = (rrf_delta / 2e-7) / (tm2c2_delta / 2e-7)
    assert lip_ratio > 100.0

    # Primary-paper arithmetic verifications:
    # 1. CodeSearchNet Table 1 exact sum across 6 languages
    csn_doc = 347789 + 542991 + 157988 + 717313 + 503502 + 57393
    csn_all = 726768 + 1569889 + 1857835 + 977821 + 1156085 + 164048
    assert csn_doc == 2326976 and csn_all == 6452446
    # 2. RepoBench-P Table 1 exact sums
    assert (10867 + 4652 + 6399) == 21918 and (10599 + 4459 + 6196) == 21254
    # 3. Cormack SIGIR 2009 Table 3: CombMNZ (0.6107) - RRF (0.6051) = +0.0056 (MAP_RRF - MAP_CombMNZ = -0.0056)
    cormack_diff = round(0.6051 - 0.6107, 4)
    assert cormack_diff == -0.0056

    print("[Probe 4] Hybrid Retrieval Normalization & RRF Analysis [Basis: documentation + derived + execution]")
    print(
        f"  Bruch Lemma 4.2 single-query equivalence (N=50): M2C2(0.72)==Z({alpha_z:.4f})==TM2C2({alpha_tmm:.4f}) -> "
        f"exact_rank_match={ord_mm == ord_z == ord_tmm}; RRF_vs_TM2C2_2e-7_slope_ratio={lip_ratio:.1f}x"
    )
    print(
        f"  [illustrative analytical model] NDCG@10 (alpha=0.80, 3x16 queries): "
        f"exact_sym(TM2C2={means['exact_symbol']['tm2c2']:.3f}, RRF={means['exact_symbol']['rrf']:.3f}), "
        f"narrow_NL(TM2C2={means['narrow_noise_nl']['tm2c2']:.3f}, M2C2={means['narrow_noise_nl']['m2c2']:.3f}, Z={means['narrow_noise_nl']['z']:.3f}), "
        f"outlier_spike(RRF={means['boilerplate_outlier']['rrf']:.3f}, TM2C2={means['boilerplate_outlier']['tm2c2']:.3f}, overall_TM2C2={overall['tm2c2']:.3f})"
    )
    print(
        f"  Paper table checks: CSN_totals=({csn_doc}, {csn_all}), "
        f"RepoBench_P=(21918, 21254), Cormack_LETOR3_RRF_minus_CombMNZ={cormack_diff:+.4f} (p~0.2)"
    )
    return {"overall": overall, "lip_ratio": lip_ratio}


# ============================================================================
# PROBE 5: Real `git` Merkle-Tree Invalidation vs. Zoekt Shard Rebuild
# ============================================================================


def git_blob_sha1(data: bytes) -> str:
    hdr = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(hdr + data).hexdigest()


def git_tree_sha1(entries: list[tuple[str, str, str]]) -> str:
    """Computes canonical Git `tree` SHA-1 from `(mode_str, name, hex_sha1)` tuples.
    Note Git sorts tree entries as if directory names had a trailing `'/'` (`base.c:df_name_compare`).
    """
    sorted_entries = sorted(
        entries, key=lambda e: (e[1] + "/" if e[0] == "40000" else e[1]).encode("utf-8")
    )
    body = bytearray()
    for mode, name, hex_sha in sorted_entries:
        body += f"{mode} {name}\0".encode("utf-8") + bytes.fromhex(hex_sha)
    hdr = f"tree {len(body)}\0".encode("ascii")
    return hashlib.sha1(hdr + body).hexdigest()


def zoekt_check_branch_limit(num_branches: int) -> Optional[str]:
    """Port of `ShardBuilder` branch limit (`index/shard_builder.go:422-424`)."""
    if num_branches > 64:
        return "too many branches"
    return None


def zoekt_index_state(
    indexed_branches: list[tuple[str, str]], target_branches: list[tuple[str, str]]
) -> str:
    """Port of `Options.IndexState` (`index/builder.go:397-448`):
    `!reflect.DeepEqual(repo.Branches, o.RepositoryDescription.Branches)` -> `IndexStateContent`.
    In default `zoekt-git-index` (`--incremental=true`, `--delta=false`, `IsDelta = false`,
    `cmd/zoekt-git-index/main.go:44, 48`), `IndexStateContent` dispatches `prepareNormalBuild`
    (`gitindex/index.go:632-636`) to rebuild 100% of files into new shards; opt-in `--delta`
    (`IsDelta = true`, `gitindex/index.go:951-1135`, `index/builder.go:702-765`) writes delta
    shards + `.meta` `FileTombstones` only when submodules are disabled, `.gitignore` and branch
    sets are unchanged, shard count stays below `DeltaShardNumberFallbackThreshold`, and shards
    are single-repo, while still ignoring uncommitted dirty worktrees.
    """
    if indexed_branches != target_branches:
        return "IndexStateContent"
    return "IndexStateEqual"


def run_probe_5() -> dict[str, object]:
    with tempfile.TemporaryDirectory() as tmpdir:
        env = {
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "HOME": tmpdir,
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_AUTHOR_NAME": "Deterministic Probe",
            "GIT_AUTHOR_EMAIL": "probe@example.invalid",
            "GIT_COMMITTER_NAME": "Deterministic Probe",
            "GIT_COMMITTER_EMAIL": "probe@example.invalid",
            "GIT_AUTHOR_DATE": "1700000000 +0000",
            "GIT_COMMITTER_DATE": "1700000000 +0000",
            "LC_ALL": "C",
        }

        def run_git(*args: str, input_bytes: Optional[bytes] = None) -> bytes:
            res = subprocess.run(
                ["git", *args],
                cwd=tmpdir,
                env=env,
                input=input_bytes,
                capture_output=True,
                check=True,
            )
            return res.stdout

        run_git("init", "-q", "-b", "main")

        # Construct deterministic 1,024-file repository (`16` pkg dirs x `8` subdirs x `8` `.go` files)
        # via `git fast-import` (~15 ms!) AND build in-memory Merkle tree to cross-verify SHA-1!
        files_c1: dict[str, bytes] = {}
        for d1 in range(16):
            for d2 in range(8):
                for f in range(8):
                    rel = f"pkg_{d1:02d}/sub_{d2:02d}/file_{f:02d}.go"
                    content = (
                        f"package sub_{d2:02d}\n"
                        f"func Handler_{d1:02d}_{d2:02d}_{f:02d}() string {{\n"
                        f'    return "v1_token_{d1:02d}_{d2:02d}_{f:02d}"\n}}\n'
                    ).encode("utf-8")
                    files_c1[rel] = content

        assert len(files_c1) == 1024

        # Build stdlib Merkle tree for C1 (1 root + 16 d1 + 128 d2 = 145 tree objects)
        tree_objects: dict[str, list[tuple[str, str, str]]] = {}
        d1_entries: list[tuple[str, str, str]] = []
        for d1 in range(16):
            d2_entries: list[tuple[str, str, str]] = []
            for d2 in range(8):
                f_entries: list[tuple[str, str, str]] = []
                for f in range(8):
                    rel = f"pkg_{d1:02d}/sub_{d2:02d}/file_{f:02d}.go"
                    b_sha = git_blob_sha1(files_c1[rel])
                    f_entries.append(("100644", f"file_{f:02d}.go", b_sha))
                sub_sha = git_tree_sha1(f_entries)
                tree_objects[sub_sha] = f_entries
                d2_entries.append(("40000", f"sub_{d2:02d}", sub_sha))
            pkg_sha = git_tree_sha1(d2_entries)
            tree_objects[pkg_sha] = d2_entries
            d1_entries.append(("40000", f"pkg_{d1:02d}", pkg_sha))
        root_sha_c1 = git_tree_sha1(d1_entries)
        tree_objects[root_sha_c1] = d1_entries
        assert len(tree_objects) == 145

        # Stream C1 and C2 (1-file edit to `pkg_05/sub_03/file_02.go`) into real `git fast-import`
        edited_path = "pkg_05/sub_03/file_02.go"
        edited_c2 = (
            b"package sub_03\n"
            b"func Handler_05_03_02_V2() string {\n"
            b'    return "v2_committed_symbol"\n}\n'
        )
        fi_buf = bytearray()
        mark = 1
        path_marks: list[tuple[str, int]] = []
        for rel in sorted(files_c1):
            raw = files_c1[rel]
            fi_buf += f"blob\nmark :{mark}\ndata {len(raw)}\n".encode("ascii") + raw + b"\n"
            path_marks.append((rel, mark))
            mark += 1
        c1_mark = mark
        mark += 1
        fi_buf += (
            f"commit refs/heads/main\nmark :{c1_mark}\n"
            f"author Deterministic Probe <probe@example.invalid> 1700000000 +0000\n"
            f"committer Deterministic Probe <probe@example.invalid> 1700000000 +0000\n"
            f"data 9\ncommit 1\n\n"
        ).encode("ascii")
        for rel, m in path_marks:
            fi_buf += f"M 100644 :{m} {rel}\n".encode("utf-8")
        fi_buf += b"\n"

        # Commit 2: modify exactly 1 file (`pkg_05/sub_03/file_02.go`)
        b2_mark = mark
        mark += 1
        c2_mark = mark
        fi_buf += f"blob\nmark :{b2_mark}\ndata {len(edited_c2)}\n".encode("ascii") + edited_c2 + b"\n"
        fi_buf += (
            f"commit refs/heads/main\nmark :{c2_mark}\n"
            f"author Deterministic Probe <probe@example.invalid> 1700000060 +0000\n"
            f"committer Deterministic Probe <probe@example.invalid> 1700000060 +0000\n"
            f"data 9\ncommit 2\n\n"
            f"from :{c1_mark}\n"
            f"M 100644 :{b2_mark} {edited_path}\n\n"
        ).encode("utf-8")

        run_git("fast-import", "--quiet", input_bytes=bytes(fi_buf))
        run_git("checkout", "-q", "-f", "main")

        git_c1_sha = run_git("rev-parse", "main~1").decode("ascii").strip()
        git_c2_sha = run_git("rev-parse", "main").decode("ascii").strip()
        git_c1_tree = run_git("rev-parse", "main~1^{tree}").decode("ascii").strip()
        git_c2_tree = run_git("rev-parse", "main^{tree}").decode("ascii").strip()
        assert git_c1_tree == root_sha_c1  # Exact 160-bit Merkle SHA-1 agreement with real `git`!

        # Build stdlib Merkle tree for C2 to count exact visited tree nodes during Merkle diff
        files_c2 = dict(files_c1)
        files_c2[edited_path] = edited_c2
        f_c2 = [
            (
                "100644",
                f"file_{f:02d}.go",
                git_blob_sha1(files_c2[f"pkg_05/sub_03/file_{f:02d}.go"]),
            )
            for f in range(8)
        ]
        sub_c2_sha = git_tree_sha1(f_c2)
        tree_objects[sub_c2_sha] = f_c2
        orig_pkg05_sha = d1_entries[5][2]
        d2_c2 = [
            ("40000", name, sub_c2_sha if name == "sub_03" else sha)
            for _, name, sha in tree_objects[orig_pkg05_sha]
        ]
        pkg05_c2_sha = git_tree_sha1(d2_c2)
        tree_objects[pkg05_c2_sha] = d2_c2
        d1_c2 = [
            ("40000", name, pkg05_c2_sha if name == "pkg_05" else sha)
            for _, name, sha in d1_entries
        ]
        root_sha_c2 = git_tree_sha1(d1_c2)
        tree_objects[root_sha_c2] = d1_c2
        assert root_sha_c2 == git_c2_tree

        # Recursive Merkle tree-diff counting visited tree pairs & child comparisons
        trees_visited = 0
        entries_compared = 0
        changed_blobs: list[tuple[str, str, str]] = []

        def merkle_diff(prefix: str, sha_a: str, sha_b: str) -> None:
            nonlocal trees_visited, entries_compared
            if sha_a == sha_b:
                return
            trees_visited += 1
            map_a = {name: (mode, h) for mode, name, h in tree_objects[sha_a]}
            map_b = {name: (mode, h) for mode, name, h in tree_objects[sha_b]}
            for name in sorted(set(map_a) | set(map_b)):
                entries_compared += 1
                mode_a, ha = map_a[name]
                mode_b, hb = map_b[name]
                if ha == hb:
                    continue
                sub_path = f"{prefix}{name}"
                if mode_b == "40000":
                    merkle_diff(f"{sub_path}/", ha, hb)
                else:
                    changed_blobs.append((sub_path, ha, hb))

        merkle_diff("", root_sha_c1, root_sha_c2)
        diff_tree_out = run_git("diff-tree", "-r", "--no-commit-id", git_c1_sha, git_c2_sha).decode("utf-8").strip()
        assert len(diff_tree_out.splitlines()) == 1 and edited_path in diff_tree_out
        assert trees_visited == 3  # root -> pkg_05 -> sub_03 (3 / 145 = 2.07%!)
        assert entries_compared == 32  # 16 + 8 + 8 = 32 vs 1,024 full-stat scan!
        assert len(changed_blobs) == 1

        # Default `zoekt-git-index` (`IsDelta=false`, `builder.go:433`) & `>64` branch overflow (`shard_builder.go:422`)
        z_state_advance = zoekt_index_state([("HEAD", git_c1_sha)], [("HEAD", git_c2_sha)])
        assert z_state_advance == "IndexStateContent"
        assert zoekt_check_branch_limit(64) is None
        assert zoekt_check_branch_limit(65) == "too many branches"

        # Two-Layer `(Committed Blob-SHA Index + Dirty Worktree Tombstone/Overlay)` Verification
        # Build token index keyed by committed `blob_sha` at C2:
        blob_token_index: dict[str, set[str]] = {}
        committed_path_to_blob: dict[str, str] = {}
        for rel, raw in files_c2.items():
            b_sha = git_blob_sha1(raw)
            committed_path_to_blob[rel] = b_sha
            if b_sha not in blob_token_index:
                blob_token_index[b_sha] = set(re.findall(r"[A-Za-z0-9_]+", raw.decode("utf-8")))

        # Mutate dirty worktree WITHOUT committing:
        #   (1) Modify `pkg_01/sub_00/file_00.go` (`v1_token_01_00_00` -> `dirty_modified_token`)
        #   (2) Delete `pkg_02/sub_00/file_00.go` (`v1_token_02_00_00` removed)
        #   (3) Add untracked `pkg_01/sub_00/new_helper.go` (`dirty_untracked_token`)
        mod_rel = "pkg_01/sub_00/file_00.go"
        del_rel = "pkg_02/sub_00/file_00.go"
        add_rel = "pkg_01/sub_00/new_helper.go"
        with open(os.path.join(tmpdir, mod_rel), "wb") as fh:
            fh.write(b'package sub_00\nfunc DirtyMod() string { return "dirty_modified_token" }\n')
        os.remove(os.path.join(tmpdir, del_rel))
        with open(os.path.join(tmpdir, add_rel), "wb") as fh:
            fh.write(b'package sub_00\nfunc DirtyNew() string { return "dirty_untracked_token" }\n')

        porcelain = run_git("status", "--porcelain", "-z", "-uall").decode("utf-8")
        tombstones: set[str] = set()
        dirty_overlay: dict[str, set[str]] = {}
        for entry in porcelain.split("\0"):
            if not entry:
                continue
            status_xy = entry[:2]
            rel_p = entry[3:]
            tombstones.add(rel_p)
            if "D" not in status_xy:
                with open(os.path.join(tmpdir, rel_p), "rb") as fh:
                    dirty_overlay[rel_p] = set(re.findall(r"[A-Za-z0-9_]+", fh.read().decode("utf-8")))

        def query_two_layer(token: str) -> set[str]:
            hits = {
                rel
                for rel, b_sha in committed_path_to_blob.items()
                if rel not in tombstones and token in blob_token_index[b_sha]
            }
            for rel, toks in dirty_overlay.items():
                if token in toks:
                    hits.add(rel)
            return hits

        assert query_two_layer("v2_committed_symbol") == {edited_path}
        assert query_two_layer("v1_token_01_00_00") == set()  # Tombstoned old content!
        assert query_two_layer("v1_token_02_00_00") == set()  # Tombstoned deleted file!
        assert query_two_layer("dirty_modified_token") == {mod_rel}
        assert query_two_layer("dirty_untracked_token") == {add_rel}

    print("[Probe 5] Real Git Merkle-Tree Invalidation & Dirty Overlay [Basis: source + execution]")
    print(
        f"  1024-file Git repo (145 trees): stdlib_Merkle_SHA1_matches_git={git_c1_tree == root_sha_c1} "
        f"(C1={git_c1_tree[:12]}, C2={git_c2_tree[:12]})"
    )
    print(
        f"  1-file commit diff: Merkle_trees_visited={trees_visited}/145 ({100.0*trees_visited/145:.2f}%), "
        f"tree_entries_checked={entries_compared}/1168 ({100.0*entries_compared/1168:.2f}%), blob_entries_checked=8/1024 (0.78%), "
        f"blobs_reindexed=1/1024 (cache_reuse=99.90%) vs Zoekt_default_IndexState='{z_state_advance}' (IsDelta=false -> 1024/1024 shard rebuild)"
    )
    print(
        f"  Branch ceiling & dirty worktree: zoekt_65_branches='{zoekt_check_branch_limit(65)}'; "
        f"two_layer_overlay(tombstones={len(tombstones)}, live_overlay={len(dirty_overlay)}, stale_hits=0, dirty_recall=2/2)"
    )
    return {"trees_visited": trees_visited, "entries_compared": entries_compared}


def main() -> None:
    print("=== Trigram Code Search, SCIP/LSIF, cAST, Hybrid Fusion & Git Merkle Verification Probe ===")
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    run_probe_5()
    print("=== ALL 5 PROBE SUITES PASSED DETERMINISTICALLY ===")


if __name__ == "__main__":
    main()
