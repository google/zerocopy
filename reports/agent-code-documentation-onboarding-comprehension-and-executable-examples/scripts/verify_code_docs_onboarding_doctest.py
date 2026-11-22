#!/usr/bin/env python3
"""Deterministic verification suite for code documentation, repository onboarding,
executable doc-example verification (CPython doctest & Rust librustdoc),
call-graph documentation drift propagation, and benchmark/metric forensics.

Pure Python 3.10+ standard library only. Zero third-party dependencies.
Bit-identical stdout across PYTHONHASHSEED values.
"""

from __future__ import annotations

import ast
from collections import Counter
from dataclasses import dataclass, field
import doctest
from enum import Enum, auto
import hashlib
import io
import math
import re
import sys
import tokenize
from typing import Any


# =============================================================================
# SHARED PURE-STDLIB BLEU-4 (Papineni et al. 2002; Chen & Cherry 2014 method4)
# =============================================================================


def _ngrams(tokens: list[str], n: int) -> Counter[tuple[str, ...]]:
    if len(tokens) < n:
        return Counter()
    return Counter(tuple(tokens[i : i + n]) for i in range(len(tokens) - n + 1))


@dataclass(frozen=True)
class _UnnormalizedRatio:
    numerator: int
    denominator: int

    def as_float(self) -> float:
        return self.numerator / self.denominator


def _modified_precision(
    references: list[list[str]], hypothesis: list[str], n: int
) -> _UnnormalizedRatio:
    counts = _ngrams(hypothesis, n)
    max_counts: dict[tuple[str, ...], int] = {}
    for ref in references:
        ref_counts = _ngrams(ref, n)
        for ng in counts:
            max_counts[ng] = max(max_counts.get(ng, 0), ref_counts.get(ng, 0))
    clipped = {ng: min(cnt, max_counts[ng]) for ng, cnt in counts.items()}
    numerator = sum(clipped.values())
    denominator = max(1, sum(counts.values()))
    return _UnnormalizedRatio(numerator, denominator)


def _closest_ref_length(references: list[list[str]], hyp_len: int) -> int:
    ref_lens = [len(r) for r in references]
    return min(ref_lens, key=lambda rl: (abs(rl - hyp_len), rl))


def _brevity_penalty(closest_ref_len: int, hyp_len: int) -> float:
    if hyp_len > closest_ref_len:
        return 1.0
    if hyp_len == 0:
        return 0.0
    return math.exp(1.0 - (closest_ref_len / hyp_len))


def nltk_corpus_bleu_components(
    list_of_references: list[list[list[str]]],
    hypotheses: list[list[str]],
    weights: tuple[float, ...] = (0.25, 0.25, 0.25, 0.25),
    chen_cherry_method4: bool = False,
    k: float = 5.0,
) -> tuple[float, float, float]:
    """Exact pure-stdlib port of nltk.translate.bleu_score.corpus_bleu + method4.

    Domain precondition: every hypothesis satisfies ``len(hypothesis) >= len(weights)``
    (>= 4 tokens for BLEU-4), where ``max(1, sum(counts.values()))`` is identical to
    upstream NLTK's ``Fraction(numerator, denominator, _normalize=False)`` (upstream
    NLTK leaves ``denominator == 0`` when ``len(hypothesis) < n``). All Probe 4 and
    Probe 5 inputs satisfy ``len(hypothesis) >= 5``, enforced via assertion below.

    Returns ``(bleu, brevity_penalty, modified_precision_geomean)`` where
    ``bleu == brevity_penalty * modified_precision_geomean`` (`BP=1.0` score is the
    third element).
    """
    assert all(
        len(h) >= len(weights) for h in hypotheses
    ), "BLEU-4 domain precondition violated: len(hypothesis) < 4"

    p_numerators: Counter[int] = Counter()
    p_denominators: Counter[int] = Counter()
    hyp_lengths = 0
    ref_lengths = 0

    for references, hypothesis in zip(list_of_references, hypotheses):
        for i in range(1, len(weights) + 1):
            p_i = _modified_precision(references, hypothesis, i)
            p_numerators[i] += p_i.numerator
            p_denominators[i] += p_i.denominator
        hyp_len = len(hypothesis)
        hyp_lengths += hyp_len
        ref_lengths += _closest_ref_length(references, hyp_len)

    bp = _brevity_penalty(ref_lengths, hyp_lengths)
    raw_p: list[_UnnormalizedRatio] = [
        _UnnormalizedRatio(p_numerators[i], max(1, p_denominators[i]))
        for i in range(1, len(weights) + 1)
    ]

    if p_numerators[1] == 0:
        return 0.0, bp, 0.0

    p_vals: list[float] = []
    if chen_cherry_method4:
        incvnt = 1
        for p_i in raw_p:
            if p_i.numerator == 0 and hyp_lengths > 1:
                smoothed_num = 1.0 / ((2**incvnt) * k / math.log(hyp_lengths))
                p_vals.append(smoothed_num / p_i.denominator)
                incvnt += 1
            else:
                p_vals.append(p_i.as_float())
    else:
        p_vals = [p_i.as_float() for p_i in raw_p]
        if any(val == 0.0 for val in p_vals):
            return 0.0, bp, 0.0

    s = 0.0
    for w_i, val in zip(weights, p_vals):
        if val <= 0.0:
            return 0.0, bp, 0.0
        s += w_i * math.log(val)
    p_geomean = math.exp(s)
    return bp * p_geomean, bp, p_geomean


def nltk_corpus_bleu(
    list_of_references: list[list[list[str]]],
    hypotheses: list[list[str]],
    weights: tuple[float, ...] = (0.25, 0.25, 0.25, 0.25),
    chen_cherry_method4: bool = False,
    k: float = 5.0,
) -> float:
    """Return standard corpus BLEU-4 (`BP * modified_precision_geomean`)."""
    bleu, _, _ = nltk_corpus_bleu_components(
        list_of_references,
        hypotheses,
        weights=weights,
        chen_cherry_method4=chen_cherry_method4,
        k=k,
    )
    return bleu


def nltk_sentence_bleu_method4(
    references: list[list[str]], hypothesis: list[str]
) -> float:
    return nltk_corpus_bleu([references], [hypothesis], chen_cherry_method4=True)


def nltk_sentence_bleu_components_method4(
    references: list[list[str]], hypothesis: list[str]
) -> tuple[float, float, float]:
    """Return ``(bleu4, bp, p_geomean_bp1)`` under Chen-Cherry ``method4`` smoothing."""
    return nltk_corpus_bleu_components(
        [references], [hypothesis], chen_cherry_method4=True
    )


def _verify_bleu_reference_vectors() -> None:
    """Self-check against NLTK's published doctests in nltk/translate/bleu_score.py."""
    hyp1 = [
        "It", "is", "a", "guide", "to", "action", "which", "ensures", "that",
        "the", "military", "always", "obeys", "the", "commands", "of", "the", "party",
    ]
    ref1a = [
        "It", "is", "a", "guide", "to", "action", "that", "ensures", "that",
        "the", "military", "will", "forever", "heed", "Party", "commands",
    ]
    ref1b = [
        "It", "is", "the", "guiding", "principle", "which", "guarantees", "the",
        "military", "forces", "always", "being", "under", "the", "command", "of", "the", "Party",
    ]
    ref1c = [
        "It", "is", "the", "practical", "guide", "for", "the", "army", "always",
        "to", "heed", "the", "directions", "of", "the", "party",
    ]
    hyp2 = [
        "he", "read", "the", "book", "because", "he", "was", "interested", "in",
        "world", "history",
    ]
    ref2a = [
        "he", "was", "interested", "in", "world", "history", "because", "he",
        "read", "the", "book",
    ]
    c_score = nltk_corpus_bleu([[ref1a, ref1b, ref1c], [ref2a]], [hyp1, hyp2])
    s_score, s_bp, s_pgeo = nltk_corpus_bleu_components([[ref1a]], [hyp1])
    assert abs(c_score - 0.5920778868801042) < 1e-9
    assert abs(s_score - 0.41180376356915777) < 1e-9
    assert s_bp == 1.0 and abs(s_score - s_pgeo) < 1e-15


# =============================================================================
# PROBE 1: Real CPython stdlib doctest Blind-Spot Matrix vs. Hardened Gate
# Pinned source reference: python/cpython@436d791c26de90e38ee1734a42534594f6a56e98
#   Lib/doctest.py:156, 293-340, 350-374, 613-624, 714-715, 1420-1424,
#                  1440, 1493-1497, 1763-1767, 1792-1795
# =============================================================================


def _make_scoped_exception(module_name: str, cls_name: str) -> type[Exception]:
    cls = type(cls_name, (Exception,), {"__module__": module_name})
    return cls


BillingQuotaError = _make_scoped_exception("billing.errors", "QuotaExceededError")
StorageQuotaError = _make_scoped_exception("storage.errors", "QuotaExceededError")


def _run_stock_doctest(doc: str, globs: dict[str, Any]) -> doctest.TestResults:
    parser = doctest.DocTestParser()
    test = parser.get_doctest(doc, dict(globs), "probe_case", "<probe>", 0)
    sink = io.StringIO()
    runner = doctest.DocTestRunner(verbose=False, optionflags=0)
    return runner.run(test, out=sink.write)


_FENCED_PY_RE = re.compile(
    r"^[ \t]*```(?P<info>python|py)(?P<mods>[^\n`]*)\n(?P<code>.*?)(?=^[ \t]*```)[ \t]*```",
    re.DOTALL | re.MULTILINE,
)

_CALL_BINDING_TYPEERROR_PATTERNS = (
    "got an unexpected keyword argument",
    "missing ",
    "takes ",
    "positional argument",
    "keyword-only argument",
)


def _single_line_structural_ellipsis_match(want: str, got: str) -> bool:
    """Line-bounded ellipsis check that refuses to match `...` across newlines."""
    want_lines = want.rstrip("\n").splitlines()
    got_lines = got.rstrip("\n").splitlines()
    if len(want_lines) != len(got_lines):
        return False
    for wl, gl in zip(want_lines, got_lines):
        if "..." not in wl:
            if wl != gl:
                return False
            continue
        parts = [re.escape(p) for p in wl.split("...")]
        pattern = "^" + ".*".join(parts) + "$"
        if not re.match(pattern, gl):
            return False
    return True


def run_hardened_doc_verifier(doc: str, globs: dict[str, Any]) -> tuple[int, int]:
    """Hardened Fence + AST-on-SKIP + Exact-Exception + Strict-Bool gate.

    Returns (failures, checked_units).
    """
    failures = 0
    checked_units = 0
    exec_globs = dict(globs)

    # 1. Verify Markdown ```python / ```py fenced blocks missed by _EXAMPLE_RE
    for match in _FENCED_PY_RE.finditer(doc):
        mods = {tok.strip() for tok in match.group("mods").replace(",", " ").split() if tok.strip()}
        code = match.group("code")
        if ">>>" in code:
            continue
        checked_units += 1
        try:
            compiled = compile(code, "<fenced-block>", "exec")
        except SyntaxError:
            failures += 1
            continue
        if "no_run" in mods or "skip" in mods:
            continue
        try:
            exec(compiled, exec_globs)
        except BaseException:
            failures += 1

    # 2. Verify interactive >>> examples with strict invariants
    parser = doctest.DocTestParser()
    examples = parser.get_examples(doc, "hardened_case")
    checker = doctest.OutputChecker()

    for idx, ex in enumerate(examples):
        checked_units += 1
        flags = ex.options

        # Always compile-check BEFORE honoring +SKIP (mirrors rustdoc `no_run`)
        try:
            code_obj = compile(ex.source, f"<doctest-ex-{idx}>", "single")
        except SyntaxError:
            if ex.exc_msg is None or not ex.exc_msg.startswith("SyntaxError"):
                failures += 1
            continue

        if flags.get(doctest.SKIP, False):
            continue

        stdout_buf = io.StringIO()
        old_stdout = sys.stdout
        exc_caught: BaseException | None = None
        snippet_tb = None
        callee_tb = None
        try:
            sys.stdout = stdout_buf
            exec(code_obj, exec_globs)
        except BaseException as exc:
            exc_caught = exc
            # Under `exec(code_obj, exec_globs)`:
            # - Frame 0 (`exc.__traceback__`) is `run_hardened_doc_verifier`.
            # - Frame 1 (`snippet_tb = exc.__traceback__.tb_next`) is `<doctest-ex-{idx}>`.
            # - Frame 2 (`callee_tb = snippet_tb.tb_next`) is the first frame inside any
            #   called function; it is `None` whenever Python raises a caller-boundary
            #   `TypeError` (e.g., renamed keyword argument) before entering the callee.
            snippet_tb = exc.__traceback__.tb_next if exc.__traceback__ is not None else None
            callee_tb = snippet_tb.tb_next if snippet_tb is not None else None
        finally:
            sys.stdout = old_stdout

        got = stdout_buf.getvalue()

        if exc_caught is None:
            if ex.exc_msg is not None:
                failures += 1
                continue
            strict_flags = doctest.DONT_ACCEPT_TRUE_FOR_1
            if flags.get(doctest.NORMALIZE_WHITESPACE, False):
                strict_flags |= doctest.NORMALIZE_WHITESPACE
            if flags.get(doctest.ELLIPSIS, False):
                if not _single_line_structural_ellipsis_match(ex.want, got):
                    failures += 1
            else:
                if not checker.check_output(ex.want, got, strict_flags):
                    failures += 1
        else:
            if ex.exc_msg is None:
                failures += 1
                continue
            exc_cls = type(exc_caught)
            actual_qual = (
                exc_cls.__qualname__
                if exc_cls.__module__ == "builtins"
                else f"{exc_cls.__module__}.{exc_cls.__qualname__}"
            )
            want_first_line = ex.exc_msg.splitlines()[0].strip()
            want_type, _, want_detail = want_first_line.partition(":")
            want_type = want_type.strip()
            want_detail = want_detail.strip()

            # Qualified exception class check (catches pkg_a.Err vs pkg_b.Err)
            if actual_qual != want_type:
                failures += 1
                continue

            actual_detail = str(exc_caught)
            # Call-signature binding guard: a caller-boundary TypeError where
            # `exc.__traceback__.tb_next.tb_next is None` (`callee_tb is None`)
            # must never satisfy a precondition test—even on class-only `TypeError\n`
            # specs lacking a `TypeError: ...` detail string.
            is_binding_type_error = (
                exc_cls is TypeError
                and snippet_tb is not None
                and callee_tb is None
                and any(pat in actual_detail for pat in _CALL_BINDING_TYPEERROR_PATTERNS)
            )
            want_expects_binding_error = any(
                pat in want_detail for pat in _CALL_BINDING_TYPEERROR_PATTERNS
            )
            if is_binding_type_error and not want_expects_binding_error:
                failures += 1
                continue

            if want_detail:
                if flags.get(doctest.ELLIPSIS, False):
                    if not _single_line_structural_ellipsis_match(want_detail, actual_detail):
                        failures += 1
                elif want_detail != actual_detail:
                    failures += 1

    return failures, checked_units


def run_probe_1() -> dict[str, Any]:
    # Evolved production APIs exhibiting realistic post-refactor drift
    def parse_port(raw: str) -> int:
        return int(raw)

    def connect(host: str, *, timeout_sec: float = 5.0) -> str:
        if timeout_sec <= 0:
            raise TypeError("timeout_sec must be positive")
        return f"{host}:{timeout_sec}"

    def enforce_quota(bytes_used: int) -> None:
        if bytes_used > 100:
            raise StorageQuotaError("storage inode quota exceeded")

    def sync_batch(drifted: bool = True) -> None:
        if drifted:
            print("Batch: start\nERROR: fatal checksum mismatch\nstatus: ok")
        else:
            print("Batch: error_rate=0.0, 42 items synced, status: ok")

    def count_admins(roles: list[str], return_bool_drift: bool = True) -> int | bool:
        n = sum(1 for r in roles if r == "admin")
        return bool(n) if return_bool_drift else n

    def upload_blob(bucket: str, *, max_retries: int = 3) -> str:
        return f"{bucket}:{max_retries}"

    globs = {
        "parse_port": parse_port,
        "connect": connect,
        "enforce_quota": enforce_quota,
        "sync_batch": sync_batch,
        "count_admins": count_admins,
        "upload_blob": upload_blob,
    }

    # Explicit two-sided non-vacuity check on class-only `TypeError\n` (want_detail == ""):
    # - `timeout=-1` fails at caller binding (`tb_next.tb_next is None`) -> caught (1 failure).
    # - `timeout_sec=-1` enters `connect` body (`tb_next.tb_next is not None`) -> passes (0 failures).
    class_only_kwarg_drift = (
        ">>> connect('db.local', timeout=-1)  # doctest: +IGNORE_EXCEPTION_DETAIL\n"
        "Traceback (most recent call last):\n"
        "TypeError\n"
    )
    class_only_body_valid = (
        ">>> connect('db.local', timeout_sec=-1)  # doctest: +IGNORE_EXCEPTION_DETAIL\n"
        "Traceback (most recent call last):\n"
        "TypeError\n"
    )
    assert _run_stock_doctest(class_only_kwarg_drift, globs).failed == 0
    assert run_hardened_doc_verifier(class_only_kwarg_drift, globs) == (1, 1)
    assert run_hardened_doc_verifier(class_only_body_valid, globs) == (0, 1)

    drift_cases: list[tuple[str, str]] = [
        (
            "fenced_markdown_no_ps1",
            "Usage:\n```python\nassert legacy_parse_port('8080') == 8080\n```\n"
            "```python\nport := :\n```\n",
        ),
        (
            "ignore_exc_renamed_kwarg",
            ">>> connect('db.local', timeout=-1)  # doctest: +IGNORE_EXCEPTION_DETAIL\n"
            "Traceback (most recent call last):\n"
            "TypeError: timeout must be positive\n"
            ">>> connect('db.local', timeout=-1)  # doctest: +IGNORE_EXCEPTION_DETAIL\n"
            "Traceback (most recent call last):\n"
            "TypeError\n",
        ),
        (
            "ignore_exc_cross_module",
            ">>> enforce_quota(250)  # doctest: +IGNORE_EXCEPTION_DETAIL\n"
            "Traceback (most recent call last):\n"
            "billing.errors.QuotaExceededError: invoice cap reached\n",
        ),
        (
            "ellipsis_multiline_error",
            ">>> sync_batch(True)  # doctest: +ELLIPSIS\n"
            "Batch: ... ok\n",
        ),
        (
            "bool_true_for_1_coercion",
            ">>> count_admins(['admin'], True)\n1\n"
            ">>> count_admins([], True)\n0\n",
        ),
        (
            "skip_uncompiled_syntax_rot",
            ">>> upload_blob('prod', retries= )  # doctest: +SKIP\n"
            "'prod:3'\n",
        ),
    ]

    valid_controls: list[tuple[str, str]] = [
        (
            "valid_fenced_markdown",
            "Usage:\n```python\nassert parse_port('8080') == 8080\n```\n",
        ),
        (
            "valid_exact_kwarg_validation",
            ">>> connect('db.local', timeout_sec=-1)\n"
            "Traceback (most recent call last):\n"
            "TypeError: timeout_sec must be positive\n"
            + class_only_body_valid,
        ),
        (
            "valid_qualified_module_exc",
            ">>> enforce_quota(250)\n"
            "Traceback (most recent call last):\n"
            "storage.errors.QuotaExceededError: storage inode quota exceeded\n",
        ),
        (
            "valid_single_line_ellipsis",
            # Includes benign `error_rate=0.0` substring to verify zero false positives
            ">>> sync_batch(False)  # doctest: +ELLIPSIS\n"
            "Batch: ... items synced, status: ok\n",
        ),
        (
            "valid_strict_int_return",
            ">>> count_admins(['admin'], False)\n1\n"
            ">>> count_admins([], False)\n0\n",
        ),
        (
            "valid_skip_syntactic_example",
            ">>> upload_blob('prod', max_retries=3)  # doctest: +SKIP\n"
            "'prod:3'\n",
        ),
    ]

    stock_caught = 0
    hardened_caught = 0
    per_case_summary: list[str] = []
    for name, doc in drift_cases:
        stock_res = _run_stock_doctest(doc, globs)
        h_fail, h_units = run_hardened_doc_verifier(doc, globs)
        if stock_res.failed > 0:
            stock_caught += 1
        if h_fail > 0:
            hardened_caught += 1
        assert stock_res.failed == 0, f"Expected stock doctest blind spot on {name}"
        assert h_fail == h_units and h_units >= 1, f"Expected hardened catch on all units in {name}"
        per_case_summary.append(
            f"{name}(stock={stock_res.failed}/{stock_res.attempted},hardened={h_fail}/{h_units})"
        )

    control_false_positives = 0
    for name, doc in valid_controls:
        h_fail, h_units = run_hardened_doc_verifier(doc, globs)
        assert h_units >= 1
        if h_fail > 0:
            control_false_positives += 1
    assert stock_caught == 0
    assert hardened_caught == len(drift_cases) == 6
    assert control_false_positives == 0

    print("PROBE 1 [Basis: source + execution (stdlib doctest)]")
    print(
        f"  Drift-detection recall across 6 API/syntax/type drift classes:"
        f" stock Lib/doctest.py = {stock_caught}/{len(drift_cases)} (0.0%),"
        f" Hardened Fence+AST+ExactExc gate = {hardened_caught}/{len(drift_cases)} (100.0%)"
    )
    print(
        "  Class-only `TypeError` call-boundary check (`tb_next.tb_next is None`):"
        " renamed-kwarg `timeout=-1` caught (1/1), callee-body `timeout_sec=-1` passed (0/1)"
    )
    print(
        f"  Valid-control false positives: {control_false_positives}/{len(valid_controls)} (0.0%);"
        f" breakdown: {', '.join(per_case_summary[:3])}"
    )
    print(f"             {', '.join(per_case_summary[3:])}")
    return {
        "stock_caught": stock_caught,
        "hardened_caught": hardened_caught,
        "control_fp": control_false_positives,
    }


# =============================================================================
# PROBE 2: rustdoc map_line, Fence Tiers, & Edition 2024 Merged-Doctest Cliff
# Pinned source reference: rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1
#   src/librustdoc/html/markdown.rs:149-190, 283, 826-843, 919-939
#   src/librustdoc/doctest/make.rs:173-187
#   src/librustdoc/doctest/runner.rs:211, 226-286
#   src/librustdoc/doctest.rs:371-428, 636-640, 726-805, 840-866
# =============================================================================


@dataclass(frozen=True)
class RustdocLine:
    kind: str  # "Hidden" | "Shown"
    text: str

    def for_html(self) -> str | None:
        # html/markdown.rs:155-160
        return self.text if self.kind == "Shown" else None

    def for_code(self) -> str:
        # html/markdown.rs:162-167
        return self.text


def rustdoc_map_line(s: str) -> RustdocLine:
    """Exact port of src/librustdoc/html/markdown.rs:177-190."""
    trimmed = s.strip()
    if trimmed.startswith("##"):
        return RustdocLine("Shown", s.replace("##", "#", 1))
    if trimmed.startswith("# "):
        return RustdocLine("Hidden", trimmed[2:])
    if trimmed == "#":
        return RustdocLine("Hidden", "")
    return RustdocLine("Shown", s)


def rustdoc_render_and_compile_views(code_block: str) -> tuple[str, str]:
    """Exact port of html/markdown.rs:283 (HTML) and L826-843 (compiled doctest)."""
    lines = code_block.splitlines()
    html_lines = [m for ln in lines if (m := rustdoc_map_line(ln).for_html()) is not None]
    code_lines = [rustdoc_map_line(ln).for_code() for ln in lines]
    return "\n".join(html_lines), "\n".join(code_lines)


class MergeDoctests(Enum):
    NEVER = auto()
    AUTO = auto()
    ALWAYS = auto()


@dataclass(frozen=True)
class RustLangString:
    # html/markdown.rs:919-939
    should_panic: bool = False
    no_run: bool = False
    ignore_all: bool = False
    test_harness: bool = False
    compile_fail: bool = False
    standalone_crate: bool = False
    error_codes: tuple[str, ...] = ()


@dataclass(frozen=True)
class ScrapedRustDoctest:
    name: str
    lang_str: RustLangString
    has_global_allocator: bool = False
    crate_attrs: str = ""
    has_macro_def: bool = False
    everything_else: str = ""
    emits_compile_error: str | None = None  # e.g., "E0382", "E0425", or None
    panics_at_runtime: bool = False

    def can_be_merged(self, mode: MergeDoctests) -> bool:
        """Exact port of src/librustdoc/doctest/make.rs:173-187."""
        opt_out = (
            self.lang_str.compile_fail
            or self.lang_str.test_harness
            or self.lang_str.standalone_crate
        )
        if mode == MergeDoctests.AUTO:
            will_probably_fail = (
                self.has_global_allocator
                or len(self.crate_attrs) > 0
                or (self.has_macro_def and ("$crate" in self.everything_else))
            )
            return (not opt_out) and (not will_probably_fail)
        return (mode != MergeDoctests.NEVER) and (not opt_out)


def evaluate_standalone_rust_doctest(test: ScrapedRustDoctest) -> tuple[bool, int]:
    """Exact oracle logic from doctest.rs:636-640, 840-910 & runner.rs:226-229.

    Returns (passed, rustc_invocations).
    """
    if test.lang_str.ignore_all:
        return True, 0

    compiled_ok = test.emits_compile_error is None
    compiler_out = "" if compiled_ok else f"error[{test.emits_compile_error}]: compile failure"

    # doctest.rs:840-866
    if compiled_ok and test.lang_str.compile_fail:
        return False, 1
    if (not compiled_ok) and test.lang_str.compile_fail:
        if test.lang_str.error_codes:
            missing = [
                code
                for code in test.lang_str.error_codes
                if f"error[{code}]" not in compiler_out
            ]
            if missing:
                return False, 1
        return True, 1
    if not compiled_ok:
        return False, 1

    # doctest.rs:636: no_run emits metadata only without binary execution
    if test.lang_str.no_run:
        return True, 1

    # doctest.rs:905-908: should_panic checks non-zero runtime exit
    if test.lang_str.should_panic:
        return test.panics_at_runtime, 1
    return (not test.panics_at_runtime), 1


def simulate_edition_doctest_batch(
    tests: list[ScrapedRustDoctest], mode: MergeDoctests
) -> tuple[int, int]:
    """Exact invocation & fallback logic of doctest.rs:371-428, 726-805 & runner.rs:198-212.

    Returns (total_rustc_invocations, failed_tests_count).
    """
    mergeable: list[ScrapedRustDoctest] = []
    standalone: list[ScrapedRustDoctest] = []
    for t in tests:
        if t.can_be_merged(mode):
            mergeable.append(t)
        else:
            standalone.append(t)

    rustc_calls = 0
    failures = 0

    if mergeable:
        # doctest.rs:726: spawn first `rustc` (`compiler.spawn()`) for `libdoctest_bundle_{ed}.rlib`
        rustc_calls += 1
        bundle_compile_failed = any(
            (not t.lang_str.ignore_all) and (t.emits_compile_error is not None)
            for t in mergeable
        )
        if not bundle_compile_failed:
            # doctest.rs:793-804: `runner_compiler.spawn()` runs ONLY when `status.success()`
            rustc_calls += 1
            for t in mergeable:
                if t.lang_str.ignore_all or t.lang_str.no_run:
                    continue
                effective_should_panic = (not t.lang_str.no_run) and t.lang_str.should_panic
                ok = t.panics_at_runtime if effective_should_panic else (not t.panics_at_runtime)
                if not ok:
                    failures += 1
        else:
            # doctest.rs:413-428: `runner_compiler` skipped (`!status.success()`);
            # push ALL mergeable doctests into `standalone_tests` (`1 + N` total `rustc` calls)
            standalone.extend(mergeable)

    for t in standalone:
        passed, calls = evaluate_standalone_rust_doctest(t)
        rustc_calls += calls
        if not passed:
            failures += 1

    return rustc_calls, failures


def run_probe_2() -> dict[str, Any]:
    # 2A: Three-way raw-string `# ` divergence & `##` escape repair
    raw_unescaped = 'let md = r#"\n  # Section\nbody\n"#;\nassert!(md.contains("# Section"));'
    html_unesc, code_unesc = rustdoc_render_and_compile_views(raw_unescaped)
    assert raw_unescaped != code_unesc
    assert code_unesc != html_unesc
    assert raw_unescaped != html_unesc
    assert 'let md = r#"\nbody\n"#;' in html_unesc  # `# Section` line vanished in HTML!
    assert 'let md = r#"\nSection\nbody\n"#;' in code_unesc  # `# ` & indent stripped in code!

    raw_escaped = 'let md = r#"\n  ## Section\nbody\n"#;\nassert!(md.contains("# Section"));'
    html_esc, code_esc = rustdoc_render_and_compile_views(raw_escaped)
    assert html_esc == code_esc
    assert "\n  # Section\nbody\n" in code_esc

    # Verify attribute `#[derive(Debug)]` & `#let` remain Shown, bare `#` becomes Hidden("")
    assert rustdoc_map_line("#[derive(Debug)]") == RustdocLine("Shown", "#[derive(Debug)]")
    assert rustdoc_map_line("#") == RustdocLine("Hidden", "")

    # Hidden compensating setup: human HTML view uses undefined `auth_ctx`, compiled view injects it
    hidden_setup_block = '# let auth_ctx = "secret";\nlet ok = !auth_ctx.is_empty();\nassert!(ok);'
    html_hidden, code_hidden = rustdoc_render_and_compile_views(hidden_setup_block)
    assert "let auth_ctx" not in html_hidden and "auth_ctx" in html_hidden
    assert "let auth_ctx" in code_hidden

    # 2B: Four-tier fence matrix — bare `compile_fail` false pass on renamed symbol (E0425 vs E0382)
    renamed_api_bare_cf = ScrapedRustDoctest(
        name="borrow_demo_bare",
        lang_str=RustLangString(compile_fail=True, error_codes=()),
        emits_compile_error="E0425",  # symbol was deleted/renamed; borrow checker never ran!
    )
    renamed_api_coded_cf = ScrapedRustDoctest(
        name="borrow_demo_coded",
        lang_str=RustLangString(compile_fail=True, error_codes=("E0382",)),
        emits_compile_error="E0425",
    )
    ignored_broken = ScrapedRustDoctest(
        name="ignored_rot",
        lang_str=RustLangString(ignore_all=True),
        emits_compile_error="E0425",
    )
    no_run_broken_sig = ScrapedRustDoctest(
        name="no_run_type_check",
        lang_str=RustLangString(no_run=True),
        emits_compile_error="E0061",  # wrong arg count caught without executing side effects!
    )

    bare_cf_pass, _ = evaluate_standalone_rust_doctest(renamed_api_bare_cf)
    coded_cf_pass, _ = evaluate_standalone_rust_doctest(renamed_api_coded_cf)
    ignore_pass, _ = evaluate_standalone_rust_doctest(ignored_broken)
    no_run_pass, _ = evaluate_standalone_rust_doctest(no_run_broken_sig)
    assert bare_cf_pass is True and coded_cf_pass is False
    assert ignore_pass is True and no_run_pass is False

    # 2C: Edition 2024 Merged-Doctest `2 -> 1 + N` invocation cliff (N = 50 mergeable + 4 opt-out)
    clean_mergeable = [
        ScrapedRustDoctest(
            name=f"doc_{i:02d}",
            lang_str=RustLangString(no_run=(i % 5 == 0), should_panic=(i % 11 == 0)),
            everything_else="let x = 1;",
            panics_at_runtime=(i % 11 == 0),
        )
        for i in range(50)
    ]
    all_ignored_mergeable = [
        ScrapedRustDoctest(name=f"ign_{i}", lang_str=RustLangString(ignore_all=True))
        for i in range(4)
    ]
    opt_outs = [
        ScrapedRustDoctest("cf_1", RustLangString(compile_fail=True, error_codes=("E0382",)), emits_compile_error="E0382"),
        ScrapedRustDoctest("feat_1", RustLangString(), crate_attrs="#![feature(never_type)]"),
        ScrapedRustDoctest("alloc_1", RustLangString(), has_global_allocator=True),
        ScrapedRustDoctest("macro_1", RustLangString(), has_macro_def=True, everything_else="macro_rules! m { () => { $crate::f() }; }"),
    ]
    assert sum(1 for t in clean_mergeable if t.can_be_merged(MergeDoctests.AUTO)) == 50
    assert sum(1 for t in opt_outs if t.can_be_merged(MergeDoctests.AUTO)) == 0
    assert simulate_edition_doctest_batch(all_ignored_mergeable, MergeDoctests.AUTO) == (2, 0)

    calls_ed2021, fails_ed2021 = simulate_edition_doctest_batch(clean_mergeable, MergeDoctests.NEVER)
    calls_ed2024_ok, fails_ed2024_ok = simulate_edition_doctest_batch(clean_mergeable, MergeDoctests.AUTO)

    one_broken_mergeable = list(clean_mergeable)
    one_broken_mergeable[17] = ScrapedRustDoctest(
        name="doc_17",
        lang_str=RustLangString(),
        everything_else="broken_call();",
        emits_compile_error="E0425",
    )
    calls_ed2024_err, fails_ed2024_err = simulate_edition_doctest_batch(
        one_broken_mergeable, MergeDoctests.AUTO
    )

    assert (calls_ed2021, fails_ed2021) == (50, 0)
    assert (calls_ed2024_ok, fails_ed2024_ok) == (2, 0)
    assert (calls_ed2024_err, fails_ed2024_err) == (51, 1)
    cliff_ratio = calls_ed2024_err / calls_ed2024_ok
    assert cliff_ratio == 25.5

    print("PROBE 2 [Basis: source + derived + execution (Python port of rust-lang/rust@342d7446)]")
    print(
        "  map_line raw-string `# Section` 3-way split: source!=(for_code='Section')!=(for_html=omitted);"
        " `## Section` restores exact parity"
    )
    print(
        f"  Fence oracle on renamed symbol (E0425 masking E0382): bare compile_fail pass={bare_cf_pass} (false pass),"
        f" compile_fail,E0382 pass={coded_cf_pass} (caught); ignore pass={ignore_pass}, no_run type-drift pass={no_run_pass}"
    )
    print(
        f"  Edition 2024 merged-doctest cliff (N=50): Ed2021={calls_ed2021} rustc calls,"
        f" Ed2024 clean={calls_ed2024_ok} calls (25.0x speedup),"
        f" Ed2024 with 1 compile error={calls_ed2024_err} calls ({cliff_ratio:.1f}x cliff, 2 -> 1 + N)"
    )
    return {
        "ed2024_clean_calls": calls_ed2024_ok,
        "ed2024_err_calls": calls_ed2024_err,
        "cliff_ratio": cliff_ratio,
    }


# =============================================================================
# PROBE 3: RepoAgent@825d9881 Cycle Breaking & Edge-Set Diffing vs. SCC+Digest
# Pinned source reference: OpenBMB/RepoAgent@825d988127d7bfd757237d9c4e8678d9104030f0
#   repo_agent/doc_meta_info.py:77-95, 633, 637-696, 752-805
# =============================================================================


class RepoAgentStatus(Enum):
    DOC_UP_TO_DATE = auto()
    DOC_HAS_NOT_BEEN_GENERATED = auto()
    CODE_CHANGED = auto()
    ADD_NEW_REFERENCER = auto()
    REFERENCER_NOT_EXIST = auto()


@dataclass
class RepoAgentItem:
    name: str
    code_content: str
    reference_who: list[str] = field(default_factory=list)     # callees
    who_reference_me: list[str] = field(default_factory=list)  # callers
    status: RepoAgentStatus = RepoAgentStatus.DOC_UP_TO_DATE
    task_id: int = -1


def repoagent_get_task_manager(
    items: list[RepoAgentItem],
) -> tuple[list[tuple[int, str, list[int]]], int]:
    """Port of the flat non-special call-edge core of RepoAgent MetaInfo.get_task_manager
    (doc_meta_info.py:633, 637-696; omits hierarchical `x.depth` pre-sort, `item.children`,
    and `special_reference_type` parameter-default secondary break level).
    """
    remaining = [it for it in items]
    by_name = {it.name: it for it in items}
    dealt: set[str] = set()
    tasks: list[tuple[int, str, list[int]]] = []
    cycle_breaks = 0
    next_id = 0

    while remaining:
        min_break_level = 10**7
        target: RepoAgentItem | None = None
        for item in remaining:
            best_break = 0
            for callee_name in item.reference_who:
                if callee_name in by_name and callee_name not in dealt:
                    best_break += 1
            if best_break == 0:
                min_break_level = -1
                target = item
                break
            if best_break < min_break_level:
                target = item
                min_break_level = best_break

        assert target is not None
        if min_break_level > 0:
            cycle_breaks += 1

        dep_ids = sorted(
            {
                by_name[callee].task_id
                for callee in target.reference_who
                if callee in by_name and by_name[callee].task_id != -1
            }
        )
        target.task_id = next_id
        tasks.append((next_id, target.name, dep_ids))
        next_id += 1
        dealt.add(target.name)
        remaining.remove(target)

    return tasks, cycle_breaks


def repoagent_load_doc_from_older_meta(
    old_items: dict[str, RepoAgentItem], new_items: dict[str, RepoAgentItem]
) -> dict[str, RepoAgentStatus]:
    """Exact port of RepoAgent load_doc_from_older_meta (doc_meta_info.py:752-805)."""
    # Pass 1 (`travel`, L752-776): own `code_content` string inequality only
    for name, old_it in old_items.items():
        if name not in new_items:
            continue
        new_it = new_items[name]
        new_it.status = old_it.status
        if old_it.code_content != new_it.code_content:
            new_it.status = RepoAgentStatus.CODE_CHANGED

    # Pass 2 (`travel2`, L781-804): `set(new_callers) == set(old_callers)` edge-set check only
    for name, old_it in old_items.items():
        if name not in new_items:
            continue
        new_it = new_items[name]
        new_callers = set(new_it.who_reference_me)
        old_callers = set(old_it.who_reference_me)
        if new_callers != old_callers and new_it.status == RepoAgentStatus.DOC_UP_TO_DATE:
            if new_callers <= old_callers:
                new_it.status = RepoAgentStatus.REFERENCER_NOT_EXIST
            else:
                new_it.status = RepoAgentStatus.ADD_NEW_REFERENCER

    return {k: v.status for k, v in new_items.items()}


def _parse_module_call_graph_and_local_contracts(
    source: str,
) -> tuple[dict[str, str], dict[str, list[str]], dict[str, dict[str, Any]]]:
    """Parse Python module via stdlib `ast` into per-function source, callees, and local contract."""
    tree = ast.parse(source)
    lines = source.splitlines()
    func_nodes: dict[str, ast.FunctionDef] = {
        node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)
    }
    func_names = set(func_nodes.keys())

    code_by_fn: dict[str, str] = {}
    callees_by_fn: dict[str, list[str]] = {}
    local_contract: dict[str, dict[str, Any]] = {}

    # Pre-collect parameter names & defaults for every function in the module
    fn_param_defaults: dict[str, tuple[list[str], dict[str, str]]] = {}
    for name, fn in sorted(func_nodes.items()):
        pos_names = [a.arg for a in fn.args.args]
        def_vals = [ast.unparse(d) for d in fn.args.defaults]
        dmap: dict[str, str] = {}
        for pname, dval in zip(pos_names[len(pos_names) - len(def_vals) :], def_vals):
            dmap[pname] = dval
        for kw_arg, kw_def in zip(fn.args.kwonlyargs, fn.args.kw_defaults):
            if kw_def is not None:
                dmap[kw_arg.arg] = ast.unparse(kw_def)
        fn_param_defaults[name] = (pos_names, dmap)

    for name, fn in sorted(func_nodes.items()):
        seg = "\n".join(lines[fn.lineno - 1 : fn.end_lineno])
        code_by_fn[name] = seg

        callees: set[str] = set()
        raises: set[str] = set()
        inherited_defaults: set[tuple[str, str, str]] = set()
        returns_none = False
        for sub in ast.walk(fn):
            if isinstance(sub, ast.Call) and isinstance(sub.func, ast.Name):
                callee_id = sub.func.id
                if callee_id in func_names and callee_id != name:
                    callees.add(callee_id)
                    callee_pos, callee_dmap = fn_param_defaults[callee_id]
                    bound_params = set(callee_pos[: len(sub.args)]) | {
                        kw.arg for kw in sub.keywords if kw.arg is not None
                    }
                    for dparam, dval in sorted(callee_dmap.items()):
                        if dparam not in bound_params:
                            inherited_defaults.add((callee_id, dparam, dval))
            if isinstance(sub, ast.Raise) and sub.exc is not None:
                if isinstance(sub.exc, ast.Call) and isinstance(sub.exc.func, ast.Name):
                    raises.add(sub.exc.func.id)
                elif isinstance(sub.exc, ast.Name):
                    raises.add(sub.exc.id)
            if isinstance(sub, ast.Return):
                if sub.value is None or (
                    isinstance(sub.value, ast.Constant) and sub.value.value is None
                ):
                    returns_none = True

        callees_by_fn[name] = sorted(callees)

        params = [
            (
                arg.arg,
                ast.unparse(arg.annotation) if arg.annotation else "",
            )
            for arg in fn.args.args + fn.args.kwonlyargs
        ]
        defaults = [ast.unparse(d) for d in fn.args.defaults] + [
            ast.unparse(d) if d is not None else "" for d in fn.args.kw_defaults
        ]
        ret_ann = ast.unparse(fn.returns) if fn.returns else ""
        local_contract[name] = {
            "params": params,
            "defaults": defaults,
            "ret_ann": ret_ann,
            "returns_none": returns_none,
            "direct_raises": sorted(raises),
            "direct_inherited_defaults": sorted(inherited_defaults),
        }

    return code_by_fn, callees_by_fn, local_contract


def tarjan_scc_condensation(
    nodes: list[str], edges: dict[str, list[str]]
) -> list[tuple[str, ...]]:
    """Deterministic Tarjan SCC returning components in leaf-first topological order."""
    index = 0
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    sccs: list[tuple[str, ...]] = []

    def strongconnect(v: str) -> None:
        nonlocal index
        indices[v] = index
        lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)

        for w in sorted(edges.get(v, [])):
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])

        if lowlink[v] == indices[v]:
            comp: list[str] = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                comp.append(w)
                if w == v:
                    break
            sccs.append(tuple(sorted(comp)))

    for n in sorted(nodes):
        if n not in indices:
            strongconnect(n)
    return sccs  # Tarjan naturally emits sink/leaf SCCs first!


def compute_transitive_contract_digests(
    nodes: list[str],
    callees_by_fn: dict[str, list[str]],
    local_contracts: dict[str, dict[str, Any]],
) -> dict[str, str]:
    """Bottom-up SCC-condensed behavioral contract digest (signature + propagated raises/nulls).

    Scope note: unconditional set-union propagation of `effective_raises` and boolean-OR
    propagation of `effective_nullable` models callers that propagate callee exceptions
    and `None` unhandled; intermediate wrappers that catch exceptions (`try ... except`)
    or coalesce `None` require handler-aware AST suppression to avoid conservative
    false-positive caller invalidations.
    """
    sccs = tarjan_scc_condensation(nodes, callees_by_fn)
    effective_raises: dict[str, set[str]] = {
        fn: set(local_contracts[fn]["direct_raises"]) for fn in nodes
    }
    effective_inherited_defaults: dict[str, set[tuple[str, str, str]]] = {
        fn: set(local_contracts[fn]["direct_inherited_defaults"]) for fn in nodes
    }
    effective_nullable: dict[str, bool] = {
        fn: bool(local_contracts[fn]["returns_none"] or "None" in local_contracts[fn]["ret_ann"])
        for fn in nodes
    }
    digests: dict[str, str] = {}

    for comp in sccs:
        # Fixed-point union inside SCC
        changed = True
        while changed:
            changed = False
            for fn in comp:
                for cal in callees_by_fn.get(fn, []):
                    before_r = len(effective_raises[fn])
                    effective_raises[fn] |= effective_raises[cal]
                    if len(effective_raises[fn]) != before_r:
                        changed = True
                    before_d = len(effective_inherited_defaults[fn])
                    effective_inherited_defaults[fn] |= effective_inherited_defaults[cal]
                    if len(effective_inherited_defaults[fn]) != before_d:
                        changed = True
                    if effective_nullable[cal] and not effective_nullable[fn]:
                        effective_nullable[fn] = True
                        changed = True

        for fn in comp:
            payload = {
                "params": local_contracts[fn]["params"],
                "defaults": local_contracts[fn]["defaults"],
                "ret_ann": local_contracts[fn]["ret_ann"],
                "nullable": effective_nullable[fn],
                "raises": sorted(effective_raises[fn]),
                "inherited_defaults": sorted(effective_inherited_defaults[fn]),
            }
            raw = repr(payload).encode("utf-8")
            digests[fn] = hashlib.sha256(raw).hexdigest()[:16]

    return digests


def run_probe_3() -> dict[str, Any]:
    repo_v1 = """
def eval_expr(tokens: list[str]) -> int:
    if not tokens:
        return 0
    return eval_call(tokens)

def eval_call(tokens: list[str]) -> int:
    if len(tokens) == 1:
        return int(tokens[0])
    return eval_expr(tokens[1:])

def leaf_token(user_id: str) -> str:
    return f"tok_{user_id}"

def svc_session(user_id: str) -> str:
    return leaf_token(user_id)

def api_login(user_id: str) -> str:
    return svc_session(user_id)

def leaf_quota(amount: int) -> int:
    return amount * 2

def svc_billing(amount: int) -> int:
    return leaf_quota(amount)

def api_checkout(amount: int) -> int:
    return svc_billing(amount)

def leaf_tls_cfg(host: str, verify_tls: bool = True) -> str:
    return f"{host}:{verify_tls}"

def svc_transport(host: str) -> str:
    return leaf_tls_cfg(host)

def api_connect(host: str) -> str:
    return svc_transport(host)

def svc_pinned_tls(host: str) -> str:
    return leaf_tls_cfg(host, verify_tls=True)

def leaf_hash(payload: str) -> int:
    total = 0
    for ch in payload:
        total += ord(ch)
    return total

def svc_checksum(payload: str) -> int:
    return leaf_hash(payload)

def api_verify(payload: str) -> int:
    return svc_checksum(payload)

def leaf_norm(tag: str) -> str:
    res = tag.strip()
    return res.lower()

def svc_tagger(tag: str) -> str:
    return leaf_norm(tag)

def api_index(tag: str) -> str:
    return svc_tagger(tag)

def leaf_audit_sink(msg: str) -> str:
    return msg

def old_caller(msg: str) -> str:
    return leaf_audit_sink(msg)
"""

    repo_v2 = """
def eval_expr(tokens: list[str]) -> int:
    if not tokens:
        return 0
    return eval_call(tokens)

def eval_call(tokens: list[str]) -> int:
    if len(tokens) == 1:
        return int(tokens[0])
    return eval_expr(tokens[1:])

def leaf_token(user_id: str) -> str | None:
    if not user_id:
        return None
    return f"tok_{user_id}"

def svc_session(user_id: str) -> str:
    return leaf_token(user_id)

def api_login(user_id: str) -> str:
    return svc_session(user_id)

def leaf_quota(amount: int) -> int:
    if amount > 1000:
        raise PermissionError("limit exceeded")
    return amount * 2

def svc_billing(amount: int) -> int:
    return leaf_quota(amount)

def api_checkout(amount: int) -> int:
    return svc_billing(amount)

def leaf_tls_cfg(host: str, verify_tls: bool = False) -> str:
    return f"{host}:{verify_tls}"

def svc_transport(host: str) -> str:
    return leaf_tls_cfg(host)

def api_connect(host: str) -> str:
    return svc_transport(host)

def svc_pinned_tls(host: str) -> str:
    return leaf_tls_cfg(host, verify_tls=True)

def leaf_hash(payload: str) -> int:
    return sum(ord(c) for c in payload)

def svc_checksum(payload: str) -> int:
    return leaf_hash(payload)

def api_verify(payload: str) -> int:
    return svc_checksum(payload)

def leaf_norm(tag: str) -> str:
    cleaned = tag.strip()
    return cleaned.lower()

def svc_tagger(tag: str) -> str:
    return leaf_norm(tag)

def api_index(tag: str) -> str:
    return svc_tagger(tag)

def leaf_audit_sink(msg: str) -> str:
    return msg

def new_caller(msg: str) -> str:
    return leaf_audit_sink(msg)
"""

    code1, cal1, loc1 = _parse_module_call_graph_and_local_contracts(repo_v1)
    code2, cal2, loc2 = _parse_module_call_graph_and_local_contracts(repo_v2)

    def _build_items(
        codes: dict[str, str], callees: dict[str, list[str]], init_status: RepoAgentStatus
    ) -> dict[str, RepoAgentItem]:
        callers: dict[str, list[str]] = {fn: [] for fn in codes}
        for fn, cals in callees.items():
            for c in cals:
                callers[c].append(fn)
        return {
            fn: RepoAgentItem(
                name=fn,
                code_content=codes[fn],
                reference_who=list(callees[fn]),
                who_reference_me=sorted(callers[fn]),
                status=init_status,
            )
            for fn in sorted(codes)
        }

    # 3A: Cycle-breaking check on eval_expr <-> eval_call
    v1_fresh_items = _build_items(code1, cal1, RepoAgentStatus.DOC_HAS_NOT_BEEN_GENERATED)
    cycle_pair = [v1_fresh_items["eval_expr"], v1_fresh_items["eval_call"]]
    tasks, cycle_breaks = repoagent_get_task_manager(cycle_pair)
    assert cycle_breaks == 1
    first_task_deps = tasks[0][2]
    assert first_task_deps == []  # First cycle member gets ZERO peer context!

    sccs_v1 = tarjan_scc_condensation(list(code1.keys()), cal1)
    cycle_sccs = [comp for comp in sccs_v1 if len(comp) > 1]
    assert cycle_sccs == [("eval_call", "eval_expr")]

    # 3B: Incremental drift propagation comparison
    old_items = _build_items(code1, cal1, RepoAgentStatus.DOC_UP_TO_DATE)
    new_items = _build_items(code2, cal2, RepoAgentStatus.DOC_HAS_NOT_BEEN_GENERATED)
    ra_statuses = repoagent_load_doc_from_older_meta(old_items, new_items)

    # Verify simultaneous caller-swap overwrite bug on `leaf_audit_sink`
    assert ra_statuses["leaf_audit_sink"] == RepoAgentStatus.ADD_NEW_REFERENCER

    # Ground-truth upstream callers affected by behavioral contract drift (fixed call edges!)
    true_stale_callers = {
        "svc_session", "api_login",
        "svc_billing", "api_checkout",
        "svc_transport", "api_connect",
    }
    # Ground-truth upstream callers of pure internal refactorings or explicitly pinned call-args
    benign_refactor_callers = {
        "svc_checksum", "api_verify",
        "svc_tagger", "api_index",
        "svc_pinned_tls",
    }

    ra_regenerated = {
        fn for fn, st in ra_statuses.items() if st != RepoAgentStatus.DOC_UP_TO_DATE
    }

    # Baseline 2: Naive transitive call-graph cone invalidation
    directly_changed = {fn for fn in code2 if fn not in code1 or code2[fn] != code1[fn]}
    naive_cone = set(directly_changed)
    rev_edges2 = {fn: new_items[fn].who_reference_me for fn in code2}
    frontier = list(directly_changed)
    while frontier:
        cur = frontier.pop()
        for caller in rev_edges2.get(cur, []):
            if caller not in naive_cone:
                naive_cone.add(caller)
                frontier.append(caller)

    # Proposed Architecture: SCC + AST Transitive Contract-Digest Invalidation
    dig1 = compute_transitive_contract_digests(list(code1.keys()), cal1, loc1)
    dig2 = compute_transitive_contract_digests(list(code2.keys()), cal2, loc2)
    contract_gated_regen = {
        fn
        for fn in code2
        if (fn not in code1)
        or (code2[fn] != code1[fn])  # own AST/body changed -> update own doc
        or (dig2[fn] != dig1[fn])    # transitive callee behavioral contract changed -> update caller doc!
    }

    ra_recall = len(ra_regenerated & true_stale_callers) / len(true_stale_callers)
    ra_fp = len(ra_regenerated & benign_refactor_callers) / len(benign_refactor_callers)

    naive_recall = len(naive_cone & true_stale_callers) / len(true_stale_callers)
    naive_fp = len(naive_cone & benign_refactor_callers) / len(benign_refactor_callers)

    digest_recall = len(contract_gated_regen & true_stale_callers) / len(true_stale_callers)
    digest_fp = len(contract_gated_regen & benign_refactor_callers) / len(benign_refactor_callers)

    assert ra_recall == 0.0 and ra_fp == 0.0
    assert naive_recall == 1.0 and naive_fp == 1.0
    assert digest_recall == 1.0 and digest_fp == 0.0

    print(
        "PROBE 3 [Basis: source + derived + execution"
        " (Python port of OpenBMB/RepoAgent@825d9881 + SCC contract model)]"
    )
    print(
        f"  Mutual-recursion cycle (eval_expr <-> eval_call): RepoAgent greedy break leaves"
        f" first node with deps={first_task_deps} (0% peer contract);"
        f" Tarjan SCC condenses {cycle_sccs[0]}"
    )
    print(
        f"  Upstream stale-caller recall on callee return/exception/default drift (6 callers, fixed edges):"
        f" RepoAgent={ra_recall*100:.1f}% (0/6), NaiveCone={naive_recall*100:.1f}% (6/6),"
        f" SCC+ContractDigest={digest_recall*100:.1f}% (6/6)"
    )
    print(
        f"  False-positive upstream caller churn on internal refactors & pinned-arg calls (5 unhandled-prop callers):"
        f" RepoAgent={ra_fp*100:.1f}% (0/5), NaiveCone={naive_fp*100:.1f}% (5/5),"
        f" SCC+ContractDigest={digest_fp*100:.1f}% (0/5)"
    )
    return {
        "repoagent_recall": ra_recall,
        "naive_fp": naive_fp,
        "digest_recall": digest_recall,
        "digest_fp": digest_fp,
    }


# =============================================================================
# PROBE 4: RepoQA@ae876deb Evaluator Forensics
# Pinned source reference: evalplus/repoqa@ae876deb1365dbf5a15b0533723c8ed123eee586
#   repoqa/compute_score.py:84-113, 162, 169-189, 307
#   repoqa/metric.py:10-21
#   scripts/curate/needle_selection.py:46-51
# =============================================================================


REPOQA_FENCE_RE = re.compile(
    r"^```(?:\w+)?\s*\n(.*?)(?=^```)```", re.DOTALL | re.MULTILINE
)
FIXED_FENCE_RE = re.compile(
    r"^[ \t]*```[^\n`]*\n(.*?)(?=^[ \t]*```)[ \t]*```", re.DOTALL | re.MULTILINE
)


def repoqa_sanitize_output(model_output: str, use_fixed_fence_re: bool = False) -> str:
    """Exact fence-extraction step of repoqa/compute_score.py:84-95, 112.

    Note: compute_score.py:100-110 applies tree-sitter `FUNCTION_QUERY[lang]` after
    fence extraction, which is never reached when `code_blocks` is empty at L93-94
    (e.g., on ```c++ or list-indented fences), returning raw `model_output` instead.
    """
    model_output = model_output.strip()
    pat = FIXED_FENCE_RE if use_fixed_fence_re else REPOQA_FENCE_RE
    code_blocks = pat.findall(model_output)
    if not code_blocks:
        return model_output
    return code_blocks[0]


def repoqa_compute_function_similarity(cand: str, ref: str) -> float:
    """Exact port of repoqa/metric.py:10-21 (`re.split(r"\\s+")` + Chen-Cherry method4)."""
    cand_tokens = [tok for tok in re.split(r"\s+", cand.strip()) if tok]
    ref_tokens = [tok for tok in re.split(r"\s+", ref.strip()) if tok]
    return nltk_sentence_bleu_method4([ref_tokens], cand_tokens)


def lexical_python_similarity(cand: str, ref: str) -> float:
    """Formatting-invariant Python token similarity using stdlib `tokenize`."""

    def _lex(src: str) -> list[str]:
        out: list[str] = []
        reader = io.BytesIO(src.encode("utf-8")).readline
        for tok in tokenize.tokenize(reader):
            if tok.type in (
                tokenize.ENCODING,
                tokenize.NEWLINE,
                tokenize.NL,
                tokenize.INDENT,
                tokenize.DEDENT,
                tokenize.COMMENT,
                tokenize.ENDMARKER,
            ):
                continue
            out.append(tok.string)
        return out

    return nltk_sentence_bleu_method4([_lex(ref)], _lex(cand))


def repoqa_needle_evaluator(
    model_output: str,
    ground_truth_name: str,
    candidates: list[tuple[str, str]],
    threshold: float = 0.8,
) -> tuple[bool, str | None, float]:
    """Exact port of repoqa/compute_score.py:164-189 + 307 (`threshold = 0.8`)."""
    sanitized = repoqa_sanitize_output(model_output)
    best_target: str | None = None
    best_sim = 0.0
    for name, func_src in candidates:
        sim = repoqa_compute_function_similarity(sanitized, func_src)
        if sim > best_sim:
            best_sim = sim
            best_target = name
    passed = (best_target == ground_truth_name) and (best_sim >= threshold)
    return passed, best_target, best_sim


def run_probe_4() -> dict[str, Any]:
    # 4A: ```c++ and indented fence failure (`compute_score.py:86`)
    cpp_needle = (
        "int32_t clamp_i32(int32_t v, int32_t lo, int32_t hi) {\n"
        "    if (v < lo) return lo;\n"
        "    if (v > hi) return hi;\n"
        "    return v;\n"
        "}"
    )
    prose = (
        "Here is the exact function retrieved from the repository context along with "
        "its boundary checks for minimum and maximum clamping thresholds on signed "
        "32-bit integers as requested by the specification:"
    )
    out_cpp_word = f"{prose}\n```cpp\n{cpp_needle}\n```"
    out_cpp_plus = f"{prose}\n```c++\n{cpp_needle}\n```"
    out_indented = f"  - {prose}\n  ```cpp\n{cpp_needle}\n  ```"

    sim_cpp_word = repoqa_compute_function_similarity(
        repoqa_sanitize_output(out_cpp_word), cpp_needle
    )
    sim_cpp_plus = repoqa_compute_function_similarity(
        repoqa_sanitize_output(out_cpp_plus), cpp_needle
    )
    sim_indented = repoqa_compute_function_similarity(
        repoqa_sanitize_output(out_indented), cpp_needle
    )
    sim_cpp_plus_fixed = repoqa_compute_function_similarity(
        repoqa_sanitize_output(out_cpp_plus, use_fixed_fence_re=True), cpp_needle
    )
    assert sim_cpp_word == 1.0
    assert sim_cpp_plus < 0.50  # Fails 0.8 threshold despite 100% exact C++ code!
    assert sim_indented < 0.55
    assert sim_cpp_plus_fixed == 1.0

    # 4B: 10-needle subsampling vs. Paper §3.2 full-F candidate pool (|F| = 64).
    # Note: scripts/curate/needle_selection.py:46-51 excludes duplicate function names
    # (`v > 1`) from needle selection while retaining distinct-named near-duplicate
    # variants (`_v0` vs `_v1`) and non-needle overloads in the full repository context `F`.
    full_f_pool: list[tuple[str, str]] = []
    for idx in range(64):
        family = idx // 4
        variant = idx % 4
        fn_name = f"dispatch_rpc_f{family:02d}_v{variant}"
        body = (
            f"def {fn_name}(ctx, req, timeout_ms={100 + family * 10}):\n"
            f"    header = ctx.build_header(req.trace_id, family={family})\n"
            f"    payload = req.encode_frame(protocol_version={variant})\n"
            f"    if not ctx.channel_ready(header):\n"
            f"        raise RuntimeError('channel unavailable for family {family}')\n"
            f"    return ctx.send_frame(header, payload, timeout_ms=timeout_ms)"
        )
        full_f_pool.append((fn_name, body))

    # Sample 10 unique-named needles from distinct chunks (families 0..9, variant 0)
    sampled_10_needles = [full_f_pool[fam * 4] for fam in range(10)]
    assert len(sampled_10_needles) == 10

    # Evaluate 10 retrieval queries: 6 exact hits (v0) + 4 wrong-variant retrievals (v1 in F \ needles)
    pass_10_needle = 0
    pass_full_f = 0
    for fam in range(10):
        gt_name, gt_code = sampled_10_needles[fam]
        returned_code = full_f_pool[fam * 4 + 1][1] if fam in (1, 3, 6, 8) else gt_code
        wrapped = f"```python\n{returned_code}\n```"
        ok_10, _, _ = repoqa_needle_evaluator(wrapped, gt_name, sampled_10_needles)
        ok_64, _, _ = repoqa_needle_evaluator(wrapped, gt_name, full_f_pool)
        pass_10_needle += int(ok_10)
        pass_full_f += int(ok_64)

    assert pass_full_f == 6
    assert pass_10_needle == 10  # +40.0 pp false-positive score inflation!

    # 4C: Whitespace BLEU tokenization sensitivity (`re.split(r"\s+")` on AST-identical code)
    py_pep8 = (
        "def compute_margin(price: float, cost: float, tax: float = 0.08) -> float:\n"
        "    gross = (price - cost) * (1.0 - tax)\n"
        "    return max(0.0, gross)"
    )
    py_compact = (
        "def compute_margin(price:float,cost:float,tax:float=0.08)->float:\n"
        "    gross=(price-cost)*(1.0-tax)\n"
        "    return max(0.0,gross)"
    )
    assert ast.dump(ast.parse(py_pep8)) == ast.dump(ast.parse(py_compact))
    ws_bleu = repoqa_compute_function_similarity(py_compact, py_pep8)
    lex_bleu = lexical_python_similarity(py_compact, py_pep8)
    ast_canon_bleu = repoqa_compute_function_similarity(
        ast.unparse(ast.parse(py_compact)), ast.unparse(ast.parse(py_pep8))
    )
    assert ws_bleu < 0.15  # Catastrophic collapse on AST-identical code!
    assert lex_bleu == 1.0 and ast_canon_bleu == 1.0

    print("PROBE 4 [Basis: source + derived + execution (Python port of evalplus/repoqa@ae876deb)]")
    print(
        f"  Fence regex (`^```(?:\\w+)?\\s*\\n`) on exact C++ needle:"
        f" ```cpp={sim_cpp_word:.3f} (PASS) vs ```c++={sim_cpp_plus:.3f} (FAIL <0.8),"
        f" indented={sim_indented:.3f} (FAIL); fixed fence regex={sim_cpp_plus_fixed:.3f}"
    )
    print(
        f"  Candidate-pool discrepancy (|F|=64 with near-duplicate variants, 4/10 wrong-variant outputs):"
        f" §3.2 full-F accuracy={pass_full_f}/10 (60.0%) vs code 10-needle loop={pass_10_needle}/10 (100.0%, +40.0 pp inflation)"
    )
    print(
        f"  AST-identical Python whitespace sensitivity: metric.py re.split('\\s+') BLEU-4={ws_bleu:.3f} (FAIL)"
        f" vs stdlib tokenize={lex_bleu:.3f} & ast.unparse={ast_canon_bleu:.3f}"
    )
    return {
        "cpp_plus_bleu": sim_cpp_plus,
        "inflation_pp": (pass_10_needle - pass_full_f) * 10.0,
        "ws_bleu": ws_bleu,
    }


# =============================================================================
# PROBE 5: BLEU-4 Surface Overlap vs. AST Contract Faithfulness Inversion
# Grounded in Panthaplackel et al. (ACL 2020), SIDE (Mastropaolo et al. ICSE 2024),
# HEBCUP (Lin et al. ICPC 2021), and DoGBench (Liu et al. 2026).
# Uses 12 structurally distinct evolved functions (`N_eff = 12` distinct BLEU-4
# and `BP=1.0` modified-precision vectors) and separates `BP = 1.0` length-matched
# paraphrases from `BP < 1.0` concise rewrites.
# =============================================================================


@dataclass(frozen=True)
class ExtractedAstContract:
    default_map: dict[str, str]
    nullable_return: bool
    raised_exceptions: tuple[str, ...]
    inclusive_bound: bool  # True if <= or >= boundary used, False if strict < or >


def extract_function_contract(fn_src: str) -> ExtractedAstContract:
    tree = ast.parse(fn_src)
    fn = next(n for n in tree.body if isinstance(n, ast.FunctionDef))
    pos_args = [a.arg for a in fn.args.args]
    default_vals = [ast.unparse(d) for d in fn.args.defaults]
    default_map: dict[str, str] = {}
    for arg_name, d_val in zip(pos_args[len(pos_args) - len(default_vals) :], default_vals):
        default_map[arg_name] = d_val
    for kw_arg, kw_def in zip(fn.args.kwonlyargs, fn.args.kw_defaults):
        if kw_def is not None:
            default_map[kw_arg.arg] = ast.unparse(kw_def)

    nullable = fn.returns is not None and ("None" in ast.unparse(fn.returns))
    raises: set[str] = set()
    has_inclusive = False
    has_strict = False
    for node in ast.walk(fn):
        if isinstance(node, ast.Return) and (
            node.value is None
            or (isinstance(node.value, ast.Constant) and node.value.value is None)
        ):
            nullable = True
        if isinstance(node, ast.Raise) and node.exc is not None:
            if isinstance(node.exc, ast.Call) and isinstance(node.exc.func, ast.Name):
                raises.add(node.exc.func.id)
            elif isinstance(node.exc, ast.Name):
                raises.add(node.exc.id)
        if isinstance(node, ast.Compare):
            for op in node.ops:
                if isinstance(op, (ast.LtE, ast.GtE)):
                    has_inclusive = True
                elif isinstance(op, (ast.Lt, ast.Gt)):
                    has_strict = True

    assert has_inclusive != has_strict, "Each benchmarked AST must have unambiguous bound polarity"
    return ExtractedAstContract(
        default_map=default_map,
        nullable_return=nullable,
        raised_exceptions=tuple(sorted(raises)),
        inclusive_bound=has_inclusive,
    )


def score_docstring_contract_faithfulness(docstring: str, contract: ExtractedAstContract) -> float:
    """Verify AST-grounded behavioral facets (defaults, nullability, exceptions, bound polarity)."""
    checks = 0
    passed = 0
    low = docstring.lower()

    # 1. Parameter default value accuracy (1 check per defaulted parameter; token-bounded)
    for param, val in sorted(contract.default_map.items()):
        checks += 1
        p_esc = re.escape(param.lower())
        v_clean = re.escape(val.strip("'\"").lower())
        eq_pat = rf"\b{p_esc}\s*=\s*['\"]?{v_clean}['\"]?(?![a-z0-9_.])"
        prose_pat = (
            rf"`{p_esc}`\s+(?:defaults\s+to|default\s+is|set\s+to|initialized\s+to)"
            rf"\s+`['\"]?{v_clean}['\"]?`"
        )
        alt_pat = rf"default\s+`{p_esc}`\s+(?:of|is)\s+`['\"]?{v_clean}['\"]?`"
        if re.search(eq_pat, low) or re.search(prose_pat, low) or re.search(alt_pat, low):
            passed += 1

    # 2. Return nullability contract (`None` vs guaranteed non-null)
    checks += 1
    mentions_none = any(
        phrase in low
        for phrase in (
            "returns `none`",
            "return `none`",
            "or `none`",
            "`none` when",
            "`none` if",
            "`none` on",
            "yields `none`",
            "yield `none`",
            "returning `none`",
        )
    )
    claims_never_none = any(
        phrase in low
        for phrase in (
            "never `none`",
            "non-null",
            "never null",
            "always returns a",
            "guaranteed non-empty",
            "always produces a",
        )
    )
    if contract.nullable_return:
        if mentions_none and not claims_never_none:
            passed += 1
    else:
        if claims_never_none and not mentions_none:
            passed += 1

    # 3. Raised exception class set accuracy (handles 0, 1, or 2+ exception classes)
    checks += 1
    doc_excs = tuple(sorted(set(re.findall(r"\b([A-Z][A-Za-z0-9_]*Error)\b", docstring))))
    claims_no_exc = any(
        phrase in low
        for phrase in ("does not raise", "never raises", "without raising", "raises no exceptions")
    )
    if not contract.raised_exceptions:
        if not doc_excs and claims_no_exc:
            passed += 1
    else:
        if doc_excs == contract.raised_exceptions and not claims_no_exc:
            passed += 1

    # 4. Boundary polarity (`inclusive` vs `strictly`)
    checks += 1
    has_inc = ("inclusive" in low) or ("inclusively" in low)
    has_strict = ("strictly" in low) or ("strict " in low)
    if contract.inclusive_bound:
        if has_inc and not has_strict:
            passed += 1
    else:
        if has_strict and not has_inc:
            passed += 1

    return passed / checks


def _word_tokens(text: str) -> list[str]:
    # Standard word/identifier tokenization (as in Panthaplackel et al. ACL 2020)
    return re.findall(r"[a-z0-9_]+", text.lower())


def _spearman_rho(xs: list[float], ys: list[float]) -> float:
    assert len(xs) == len(ys) and len(xs) > 2

    def _ranks(vals: list[float]) -> list[float]:
        indexed = sorted(enumerate(vals), key=lambda iv: iv[1])
        out = [0.0] * len(vals)
        i = 0
        while i < len(indexed):
            j = i
            while j + 1 < len(indexed) and indexed[j + 1][1] == indexed[i][1]:
                j += 1
            avg_rank = (i + j) / 2.0 + 1.0
            for m in range(i, j + 1):
                out[indexed[m][0]] = avg_rank
            i = j + 1
        return out

    rx = _ranks(xs)
    ry = _ranks(ys)
    mx = sum(rx) / len(rx)
    my = sum(ry) / len(ry)
    num = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    den = math.sqrt(sum((a - mx) ** 2 for a in rx) * sum((b - my) ** 2 for b in ry))
    return num / den if den > 0 else 0.0


@dataclass(frozen=True)
class EvolvedDocCase:
    name: str
    evolved_code: str
    gold_doc: str
    stale_copy: str
    single_token: str
    assumption_guess: str
    faithful_length_matched: str
    faithful_concise: str


def _build_diverse_probe_5_cases() -> list[EvolvedDocCase]:
    """12 structurally distinct evolved functions varying arity, defaults, nullability,
    exception cardinality (0, 1, or 2), boundary operators, and prose docstring styles/lengths.
    """
    return [
        # 1. 2 args, 1 default (int), nullable=True, 1 exc, inclusive (>=)
        EvolvedDocCase(
            name="fetch_record",
            evolved_code=(
                "def fetch_record(key: str, timeout_ms: int = 250) -> dict[str, str] | None:\n"
                "    if len(key) >= 128:\n"
                "        raise TimeoutError('key lookup window exceeded')\n"
                "    if not key:\n"
                "        return None\n"
                "    return {'key': key, 'timeout': str(timeout_ms)}\n"
            ),
            gold_doc=(
                "Look up a cached record dictionary for `key` within the RPC budget "
                "(`timeout_ms=250` by default). Returns `None` when `key` is empty, and "
                "raises `TimeoutError` if the key length reaches `128` bytes inclusive."
            ),
            stale_copy=(
                "Look up a cached record dictionary for `key` within the RPC budget "
                "(`timeout_ms=1000` by default). Always returns a non-null mapping, and "
                "raises `ValueError` if the key length is strictly above `128` bytes."
            ),
            single_token=(
                "Look up a cached record dictionary for `key` within the RPC budget "
                "(`timeout_ms=250` by default). Always returns a non-null mapping, and "
                "raises `ValueError` if the key length is strictly above `128` bytes."
            ),
            assumption_guess=(
                "Fetch a cached entry mapping for `key` (`timeout_ms=1000`). "
                "Produces a non-null dictionary and raises `TimeoutError` when key "
                "size is strictly above `128`."
            ),
            faithful_length_matched=(
                "Retrieve the key-value entry in cache associated with `key`, where `timeout_ms` "
                "defaults to `250` milliseconds per request. Empty keys yield `None` immediately, "
                "whereas inputs of `128` characters or more inclusive trigger `TimeoutError`."
            ),
            faithful_concise=(
                "`fetch_record` (`timeout_ms=250`): returns `None` on empty `key`; "
                "lengths `>= 128` inclusive raise `TimeoutError`."
            ),
        ),
        # 2. 3 args (kw-only), 2 defaults (int, bool), nullable=False, 2 excs, strict (>)
        EvolvedDocCase(
            name="allocate_slab",
            evolved_code=(
                "def allocate_slab(pages: int, *, max_pages: int = 256, zero_fill: bool = True) -> bytes:\n"
                "    if pages > max_pages:\n"
                "        raise MemoryError('page cap exceeded')\n"
                "    if not zero_fill:\n"
                "        raise PermissionError('unzeroed slabs forbidden')\n"
                "    return b'\\x00' * pages\n"
            ),
            gold_doc=(
                "Provision a contiguous byte buffer for `pages` memory frames in the arena "
                "allocator using `max_pages=256` and `zero_fill=True` unless overridden by "
                "the caller. Always returns a non-null `bytes` slab; raises `MemoryError` when "
                "`pages` is strictly greater than `max_pages` and `PermissionError` if unzeroed "
                "allocation is requested."
            ),
            stale_copy=(
                "Provision a contiguous byte buffer for `pages` memory frames in the arena "
                "allocator using `max_pages=64` and `zero_fill=False` unless overridden by "
                "the caller. Returns `None` when capacity is exhausted, or raises `OSError` when "
                "`pages` reaches `max_pages` inclusive during reservation."
            ),
            single_token=(
                "Provision a contiguous byte buffer for `pages` memory frames in the arena "
                "allocator using `max_pages=256` and `zero_fill=False` unless overridden by "
                "the caller. Returns `None` when capacity is exhausted, or raises `OSError` when "
                "`pages` reaches `max_pages` inclusive during reservation."
            ),
            assumption_guess=(
                "Allocate an arena buffer of `pages` frames (`max_pages=256`, `zero_fill=True`). "
                "Returns `None` when memory is full, or raises `MemoryError` at `max_pages` inclusive."
            ),
            faithful_length_matched=(
                "Reserve an initialized byte region spanning `pages` blocks in local heap memory "
                "with default `max_pages` of `256` and `zero_fill` set to `True` for tenant isolation. "
                "This helper never null-returns—it always produces a `bytes` object, raising "
                "`MemoryError` strictly above `max_pages` and `PermissionError` whenever zeroing "
                "is disabled."
            ),
            faithful_concise=(
                "Non-null slab allocator (`max_pages=256`, `zero_fill=True`); raises "
                "`MemoryError` strictly above cap and `PermissionError` if unzeroed."
            ),
        ),
        # 3. 3 args, 1 default (float), nullable=False, 0 excs (clamping!), inclusive (<=)
        EvolvedDocCase(
            name="clamp_backoff",
            evolved_code=(
                "def clamp_backoff(attempt: int, base_sec: float, jitter_ratio: float = 0.15) -> float:\n"
                "    if attempt <= 0:\n"
                "        return 0.0\n"
                "    return base_sec * attempt * (1.0 + jitter_ratio)\n"
            ),
            gold_doc=(
                "Compute retry delay in seconds from `attempt` and `base_sec` with "
                "`jitter_ratio=0.15`. Always returns a non-null float (`0.0` for `attempt` "
                "at or below `0` inclusive) and never raises exceptions."
            ),
            stale_copy=(
                "Compute retry delay in seconds from `attempt` and `base_sec` with "
                "`jitter_ratio=0.5`. Returns `None` when backoff is disabled (for `attempt` "
                "strictly below `0`) and raises `ValueError` on invalid inputs."
            ),
            single_token=(
                "Compute retry delay in seconds from `attempt` and `base_sec` with "
                "`jitter_ratio=0.15`. Returns `None` when backoff is disabled (for `attempt` "
                "strictly below `0`) and raises `ValueError` on invalid inputs."
            ),
            assumption_guess=(
                "Return a non-null backoff interval for `attempt` and `base_sec` (`jitter_ratio=0.15`), "
                "clamping values strictly below `0` and raising `ValueError` on bad ratios."
            ),
            faithful_length_matched=(
                "Calculate retry duration from `attempt` and `base_sec`, where "
                "`jitter_ratio` defaults to `0.15`. `attempt` values up to `0` "
                "inclusive evaluate to `0.0`, producing a non-null float without "
                "raising any error."
            ),
            faithful_concise=(
                "Always returns a non-null delay (`jitter_ratio=0.15`), clamping `<= 0` "
                "inclusive without raising."
            ),
        ),
        # 4. 2 args (kw-only str default), nullable=True, 1 exc, strict (<)
        EvolvedDocCase(
            name="decode_wire_header",
            evolved_code=(
                "def decode_wire_header(raw: bytes, *, encoding: str = 'utf-8') -> str | None:\n"
                "    if len(raw) < 4:\n"
                "        return None\n"
                "    if raw[:2] != b'WH':\n"
                "        raise UnicodeError('bad magic prefix')\n"
                "    return raw[2:].decode(encoding)\n"
            ),
            gold_doc=(
                "Parse a framed wire header from `raw` bytes using character codec "
                "`encoding='utf-8'`. Buffers with length strictly less than `4` bytes "
                "return `None`; malformed magic bytes raise `UnicodeError`."
            ),
            stale_copy=(
                "Parse a framed wire header from `raw` bytes using character codec "
                "`encoding='ascii'`. Buffers up to `4` bytes inclusive still produce a "
                "non-null string; malformed magic bytes raise `SyntaxError`."
            ),
            single_token=(
                "Parse a framed wire header from `raw` bytes using character codec "
                "`encoding='utf-8'`. Buffers up to `4` bytes inclusive still produce a "
                "non-null string; malformed magic bytes raise `SyntaxError`."
            ),
            assumption_guess=(
                "Decode wire packet `raw` under `encoding='utf-8'`. Payloads up to `4` bytes "
                "inclusive return `None`, while bad headers raise `SyntaxError`."
            ),
            faithful_length_matched=(
                "Extract the text payload from `raw` packet bytes with `encoding` initialized "
                "to `'utf-8'`. Short frames strictly under `4` bytes yield `None`, "
                "while invalid header prefixes trigger `UnicodeError` immediately."
            ),
            faithful_concise=(
                "Decodes header (`encoding='utf-8'`); returns `None` strictly under 4 bytes "
                "or raises `UnicodeError`."
            ),
        ),
        # 5. 4 args, 2 defaults (bool, int), nullable=True, 2 excs, inclusive (>=)
        EvolvedDocCase(
            name="open_tls_channel",
            evolved_code=(
                "def open_tls_channel(host: str, port: int, verify_cert: bool = True, handshake_sec: int = 10) -> str | None:\n"
                "    if not host:\n"
                "        return None\n"
                "    if port >= 65536:\n"
                "        raise OverflowError('port out of 16-bit range')\n"
                "    if not verify_cert:\n"
                "        raise ConnectionError('plaintext fallback disabled')\n"
                "    return f'{host}:{port}:{handshake_sec}'\n"
            ),
            gold_doc=(
                "Establish an authenticated TLS session endpoint to `host` and `port` "
                "(configured with `verify_cert=True` and `handshake_sec=10`). When `host` "
                "is blank the call returns `None`; ports `>= 65536` inclusive raise "
                "`OverflowError`, and disabling certificate verification raises `ConnectionError`."
            ),
            stale_copy=(
                "Establish an authenticated TLS session endpoint to `host` and `port` "
                "(configured with `verify_cert=False` and `handshake_sec=30`). Always returns "
                "a non-null endpoint handle; ports strictly above `65536` raise `OSError` "
                "during socket setup."
            ),
            single_token=(
                "Establish an authenticated TLS session endpoint to `host` and `port` "
                "(configured with `verify_cert=True` and `handshake_sec=30`). Always returns "
                "a non-null endpoint handle; ports strictly above `65536` raise `OSError` "
                "during socket setup."
            ),
            assumption_guess=(
                "Open a TLS connection to `host` and `port` (`verify_cert=True`, `handshake_sec=30`). "
                "Blank hosts return `None`, while ports strictly above `65536` raise `ConnectionError`."
            ),
            faithful_length_matched=(
                "Dial a verified TLS transport target for `host` and `port`, with "
                "`verify_cert` set to `True` and `handshake_sec` defaults to `10`. Blank hosts "
                "yield `None`, whereas ports from `65536` inclusive raise "
                "`OverflowError` and unverified peers raise `ConnectionError`."
            ),
            faithful_concise=(
                "TLS dialer (`verify_cert=True`, `handshake_sec=10`): returns `None` on empty "
                "host; `>= 65536` inclusive raises `OverflowError`, unverified raises `ConnectionError`."
            ),
        ),
        # 6. 2 args, 1 default (bool), nullable=False, 1 exc, inclusive (<=)
        EvolvedDocCase(
            name="commit_wal_segment",
            evolved_code=(
                "def commit_wal_segment(entries: list[str], *, fsync_now: bool = True) -> int:\n"
                "    if len(entries) <= 0:\n"
                "        raise BufferError('empty write-ahead batch')\n"
                "    return len(entries) + int(fsync_now)\n"
            ),
            gold_doc=(
                "Append `entries` to the write-ahead log segment (`fsync_now=True`) and "
                "return a non-null committed record count. Raises `BufferError` whenever "
                "the batch length is `0` or below inclusive."
            ),
            stale_copy=(
                "Append `entries` to the write-ahead log segment (`fsync_now=False`) or "
                "return `None` when nothing was flushed. Raises `RuntimeError` whenever "
                "the batch length is strictly less than `0`."
            ),
            single_token=(
                "Append `entries` to the write-ahead log segment (`fsync_now=True`) or "
                "return `None` when nothing was flushed. Raises `RuntimeError` whenever "
                "the batch length is strictly less than `0`."
            ),
            assumption_guess=(
                "Write `entries` to the WAL (`fsync_now=True`), returning a non-null count "
                "or raising `RuntimeError` when length is strictly under `0`."
            ),
            faithful_length_matched=(
                "Flush `entries` into durable log storage with `fsync_now` set to `True`, "
                "producing a guaranteed non-null integer entry count. An input batch of "
                "size `0` inclusive immediately raises `BufferError`."
            ),
            faithful_concise=(
                "Durable WAL flush (`fsync_now=True`): never `None`; size `<= 0` inclusive "
                "raises `BufferError`."
            ),
        ),
        # 7. 3 args, 1 default (int), nullable=True, 1 exc, strict (>)
        EvolvedDocCase(
            name="claim_worker_lease",
            evolved_code=(
                "def claim_worker_lease(worker_id: str, epoch: int, ttl_sec: int = 15) -> tuple[int, int] | None:\n"
                "    if epoch > 10000:\n"
                "        raise LookupError('stale coordinator epoch')\n"
                "    if not worker_id:\n"
                "        return None\n"
                "    return (epoch, ttl_sec)\n"
            ),
            gold_doc=(
                "Acquire a fenced execution lease tuple `(epoch, ttl_sec)` for `worker_id` "
                "at `epoch` using `ttl_sec=15`. Empty worker identifiers return `None`, while "
                "an `epoch` strictly exceeding `10000` raises `LookupError`."
            ),
            stale_copy=(
                "Acquire a fenced execution lease tuple `(epoch, ttl_sec)` for `worker_id` "
                "at `epoch` using `ttl_sec=60`. Always returns a non-null tuple, while "
                "an `epoch` of `10000` or higher inclusive raises `KeyError`."
            ),
            single_token=(
                "Acquire a fenced execution lease tuple `(epoch, ttl_sec)` for `worker_id` "
                "at `epoch` using `ttl_sec=15`. Always returns a non-null tuple, while "
                "an `epoch` of `10000` or higher inclusive raises `KeyError`."
            ),
            assumption_guess=(
                "Claim lease `(epoch, ttl_sec)` for `worker_id` (`ttl_sec=60`). Blank IDs "
                "return `None`, and epochs `>= 10000` inclusive raise `LookupError`."
            ),
            faithful_length_matched=(
                "Grant a `(epoch, ttl_sec)` lease pair to `worker_id` with default `ttl_sec` "
                "of `15` on the fence. Missing worker IDs yield `None`, and "
                "epochs strictly above `10000` raise `LookupError`."
            ),
            faithful_concise=(
                "Lease grant (`ttl_sec=15`): returns `None` if `worker_id` empty; `epoch > 10000` "
                "strictly raises `LookupError`."
            ),
        ),
        # 8. 3 args, 2 defaults (int, str), nullable=False, 1 exc, inclusive (>=)
        EvolvedDocCase(
            name="partition_tokens",
            evolved_code=(
                "def partition_tokens(text: str, chunk_len: int = 64, sep: str = '|') -> list[str]:\n"
                "    if chunk_len >= 4096:\n"
                "        raise ValueError('chunk_len exceeds page ceiling')\n"
                "    return [seg for seg in text.split(sep) if seg][:chunk_len]\n"
            ),
            gold_doc=(
                "Split `text` on delimiter `sep='|'` and cap the output list at "
                "`chunk_len=64` segments. Always returns a non-null `list[str]` slice, "
                "and raises `ValueError` if `chunk_len` is `4096` or larger inclusive."
            ),
            stale_copy=(
                "Split `text` on delimiter `sep=','` and cap the output list at "
                "`chunk_len=16` segments. Returns `None` when `text` is blank, "
                "and raises `IndexError` if `chunk_len` is strictly above `4096`."
            ),
            single_token=(
                "Split `text` on delimiter `sep=','` and cap the output list at "
                "`chunk_len=64` segments. Returns `None` when `text` is blank, "
                "and raises `IndexError` if `chunk_len` is strictly above `4096`."
            ),
            assumption_guess=(
                "Divide `text` by `sep='|'` into at most `chunk_len=16` parts, returning "
                "a non-null list or raising `ValueError` strictly above `4096`."
            ),
            faithful_length_matched=(
                "Segment `text` around `sep` set to `'|'` and retain up to `chunk_len` "
                "defaults to `64` non-empty items. Produces a non-null token list in all "
                "cases, raising `ValueError` from `4096` inclusive upward."
            ),
            faithful_concise=(
                "Non-null splitter (`chunk_len=64`, `sep='|'`); `chunk_len >= 4096` inclusive "
                "raises `ValueError`."
            ),
        ),
        # 9. 2 args, 1 default (int), nullable=False, 0 excs, strict (<)
        EvolvedDocCase(
            name="within_rate_window",
            evolved_code=(
                "def within_rate_window(elapsed_sec: int, window_sec: int = 30) -> bool:\n"
                "    if elapsed_sec < window_sec:\n"
                "        return True\n"
                "    return False\n"
            ),
            gold_doc=(
                "Evaluate whether `elapsed_sec` falls strictly below `window_sec=30` "
                "seconds. Always returns a non-null boolean flag and does not raise "
                "exceptions on expired timestamps."
            ),
            stale_copy=(
                "Evaluate whether `elapsed_sec` falls within `window_sec=300` seconds "
                "inclusive. Returns `None` on negative clocks and raises `AssertionError` "
                "on expired timestamps."
            ),
            single_token=(
                "Evaluate whether `elapsed_sec` falls within `window_sec=30` seconds "
                "inclusive. Returns `None` on negative clocks and raises `AssertionError` "
                "on expired timestamps."
            ),
            assumption_guess=(
                "Test if `elapsed_sec` is within `window_sec=30` inclusive, returning a "
                "non-null boolean or raising `AssertionError` when expired."
            ),
            faithful_length_matched=(
                "Check that `elapsed_sec` remains strictly less than "
                "`window_sec` defaults to `30` interval. Always produces a boolean result "
                "(never `None`) without raising any runtime error."
            ),
            faithful_concise=(
                "Non-null boolean check (`window_sec=30`): True strictly below window, "
                "never raises."
            ),
        ),
        # 10. 3 args, 1 default (int), nullable=True, 2 excs, strict (<)
        EvolvedDocCase(
            name="poll_batch_queue",
            evolved_code=(
                "def poll_batch_queue(depth: int, closed: bool, batch_size: int = 32) -> int | None:\n"
                "    if closed:\n"
                "        raise EOFError('queue closed')\n"
                "    if batch_size < 1:\n"
                "        raise ValueError('batch_size must be positive')\n"
                "    if depth == 0:\n"
                "        return None\n"
                "    return min(depth, batch_size)\n"
            ),
            gold_doc=(
                "Drain up to `batch_size=32` ready items from a queue of current `depth` "
                "unless `closed` is set. Returns `None` when `depth` is zero; raises "
                "`EOFError` if `closed` is true and `ValueError` when `batch_size` is "
                "strictly below `1`."
            ),
            stale_copy=(
                "Drain up to `batch_size=128` ready items from a queue of current `depth` "
                "unless `closed` is set. Always returns a non-null integer count; raises "
                "`TimeoutError` when `batch_size` is `1` or less inclusive."
            ),
            single_token=(
                "Drain up to `batch_size=32` ready items from a queue of current `depth` "
                "unless `closed` is set. Always returns a non-null integer count; raises "
                "`TimeoutError` when `batch_size` is `1` or less inclusive."
            ),
            assumption_guess=(
                "Poll up to `batch_size=32` items given `depth` and `closed`. Returns `None` "
                "at zero depth, and raises `EOFError` for `batch_size <= 1` inclusive."
            ),
            faithful_length_matched=(
                "Pop at most `batch_size` defaults to `32` queued messages from the active buffer "
                "given `depth` and `closed` state. Empty queues yield `None` immediately, closed channels "
                "raise `EOFError` at runtime, and any `batch_size` strictly under `1` raises `ValueError`."
            ),
            faithful_concise=(
                "Queue pop (`batch_size=32`): returns `None` when empty; raises `EOFError` "
                "if closed or `ValueError` strictly below `1`."
            ),
        ),
        # 11. 4 args (kw-only), 2 defaults (int, float), nullable=True, 1 exc, inclusive (<=)
        EvolvedDocCase(
            name="sample_trace_span",
            evolved_code=(
                "def sample_trace_span(trace_id: str, latency_ms: float, *, min_ms: int = 50, rate: float = 0.25) -> float | None:\n"
                "    if latency_ms <= min_ms:\n"
                "        return None\n"
                "    if not trace_id:\n"
                "        raise KeyError('missing trace_id')\n"
                "    return latency_ms * rate\n"
            ),
            gold_doc=(
                "Weight slow span `trace_id` of duration `latency_ms` using threshold "
                "`min_ms=50` and sampling factor `rate=0.25`. Spans with `latency_ms` "
                "at or below `min_ms` inclusive return `None`, while an empty `trace_id` "
                "raises `KeyError`."
            ),
            stale_copy=(
                "Weight slow span `trace_id` of duration `latency_ms` using threshold "
                "`min_ms=200` and sampling factor `rate=1.0`. Always returns a non-null "
                "weighted score for spans strictly below `min_ms`, while an empty `trace_id` "
                "raises `RuntimeError`."
            ),
            single_token=(
                "Weight slow span `trace_id` of duration `latency_ms` using threshold "
                "`min_ms=50` and sampling factor `rate=1.0`. Always returns a non-null "
                "weighted score for spans strictly below `min_ms`, while an empty `trace_id` "
                "raises `RuntimeError`."
            ),
            assumption_guess=(
                "Score span `trace_id` (`min_ms=50`, `rate=1.0`), returning `None` strictly "
                "below `min_ms` and raising `KeyError` on missing trace IDs."
            ),
            faithful_length_matched=(
                "Compute sampled span weight for `trace_id` with `min_ms` set to `50` and "
                "default `rate` of `0.25` on slow traces. Latencies up to `min_ms` "
                "inclusive yield `None`, and missing trace identifiers raise `KeyError`."
            ),
            faithful_concise=(
                "Span sampler (`min_ms=50`, `rate=0.25`): returns `None` for `<= min_ms` "
                "inclusive; empty ID raises `KeyError`."
            ),
        ),
        # 12. 2 args, 1 default (int), nullable=False, 1 exc, inclusive (>=)
        EvolvedDocCase(
            name="route_replica_shard",
            evolved_code=(
                "def route_replica_shard(tenant_hash: int, replica_count: int = 8) -> str:\n"
                "    if replica_count >= 64:\n"
                "        raise RuntimeError('shard ring limit exceeded')\n"
                "    return f'shard-{tenant_hash % replica_count}'\n"
            ),
            gold_doc=(
                "Map `tenant_hash` onto a shard identifier across `replica_count=8` "
                "ring partitions. Always returns a non-null shard name string, and raises "
                "`RuntimeError` when `replica_count` is `64` or greater inclusive."
            ),
            stale_copy=(
                "Map `tenant_hash` onto a shard identifier across `replica_count=3` "
                "ring partitions. Returns `None` if routing is offline, and raises "
                "`KeyError` when `replica_count` is strictly greater than `64`."
            ),
            single_token=(
                "Map `tenant_hash` onto a shard identifier across `replica_count=8` "
                "ring partitions. Returns `None` if routing is offline, and raises "
                "`KeyError` when `replica_count` is strictly greater than `64`."
            ),
            assumption_guess=(
                "Select a shard string for `tenant_hash` (`replica_count=3`), returning a "
                "non-null label or raising `RuntimeError` strictly above `64`."
            ),
            faithful_length_matched=(
                "Resolve the consistent ring target label for `tenant_hash` where `replica_count` "
                "defaults to `8` active replicas. Guaranteed non-empty string output (never "
                "`None`), raising `RuntimeError` whenever `replica_count` hits `64` inclusive."
            ),
            faithful_concise=(
                "Non-null ring router (`replica_count=8`); `>= 64` inclusive raises "
                "`RuntimeError`."
            ),
        ),
    ]


def run_probe_5() -> dict[str, Any]:
    cases = _build_diverse_probe_5_cases()
    assert len(cases) == 12

    system_names = (
        "Stale-Copy",
        "Single-Token",
        "Assumption-Guess",
        "Faithful-LengthMatched",
        "Faithful-Concise",
    )
    bleu_by_sys: dict[str, list[float]] = {k: [] for k in system_names}
    pgeo_by_sys: dict[str, list[float]] = {k: [] for k in system_names}
    bp_by_sys: dict[str, list[float]] = {k: [] for k in system_names}
    faith_by_sys: dict[str, list[float]] = {k: [] for k in system_names}

    distinct_bleu_vectors: set[tuple[float, ...]] = set()
    distinct_pgeo_vectors: set[tuple[float, ...]] = set()
    distinct_contracts: set[tuple[Any, ...]] = set()

    # Track rank correlation both across BP=1.0 length-matched 4-candidate pool (48 items)
    # and across full 5-candidate pool including concise rewrites (60 items).
    lm4_bleus: list[float] = []
    lm4_pgeos: list[float] = []
    lm4_faiths: list[float] = []
    all5_bleus: list[float] = []
    all5_pgeos: list[float] = []
    all5_faiths: list[float] = []

    bleu_top1_faithful_lm4 = 0
    pgeo_top1_faithful_lm4 = 0
    bleu_top1_faithful_all5 = 0
    ast_top1_faithful_lm4 = 0

    for case in cases:
        contract = extract_function_contract(case.evolved_code)
        distinct_contracts.add(
            (
                tuple(sorted(contract.default_map.items())),
                contract.nullable_return,
                contract.raised_exceptions,
                contract.inclusive_bound,
            )
        )
        ref_tokens = _word_tokens(case.gold_doc)
        assert score_docstring_contract_faithfulness(case.gold_doc, contract) == 1.0, (
            f"gold_doc failed faithfulness on {case.name}"
        )

        cands = {
            "Stale-Copy": case.stale_copy,
            "Single-Token": case.single_token,
            "Assumption-Guess": case.assumption_guess,
            "Faithful-LengthMatched": case.faithful_length_matched,
            "Faithful-Concise": case.faithful_concise,
        }

        # Enforce exact token-length equality (`len(hyp) == len(ref)`, `BP == 1.0`)
        # on Faithful-LengthMatched so zero brevity penalty or length inflation occurs!
        lm_tokens = _word_tokens(case.faithful_length_matched)
        concise_tokens = _word_tokens(case.faithful_concise)
        assert len(lm_tokens) == len(ref_tokens), (
            f"Faithful-LengthMatched length mismatch vs gold_doc on {case.name}: "
            f"{len(lm_tokens)} != {len(ref_tokens)}"
        )
        assert len(concise_tokens) < len(ref_tokens), (
            f"Faithful-Concise not shorter than gold_doc on {case.name}"
        )

        vec_b4: list[float] = []
        vec_pg: list[float] = []
        fn_lm4: list[tuple[str, float, float, float]] = []
        fn_all5: list[tuple[str, float, float, float]] = []

        for sys_name in system_names:
            cand_doc = cands[sys_name]
            b4, bp, pgeo = nltk_sentence_bleu_components_method4(
                [ref_tokens], _word_tokens(cand_doc)
            )
            cf = score_docstring_contract_faithfulness(cand_doc, contract)
            bleu_by_sys[sys_name].append(b4)
            pgeo_by_sys[sys_name].append(pgeo)
            bp_by_sys[sys_name].append(bp)
            faith_by_sys[sys_name].append(cf)
            vec_b4.append(round(b4, 12))
            vec_pg.append(round(pgeo, 12))

            all5_bleus.append(b4)
            all5_pgeos.append(pgeo)
            all5_faiths.append(cf)
            fn_all5.append((sys_name, b4, pgeo, cf))

            if sys_name != "Faithful-Concise":
                lm4_bleus.append(b4)
                lm4_pgeos.append(pgeo)
                lm4_faiths.append(cf)
                fn_lm4.append((sys_name, b4, pgeo, cf))

        assert faith_by_sys["Stale-Copy"][-1] == 0.0, f"Stale-Copy non-zero on {case.name}"
        assert 0.0 < faith_by_sys["Single-Token"][-1] < 1.0, f"Single-Token bounds on {case.name}"
        assert 0.0 < faith_by_sys["Assumption-Guess"][-1] < 1.0, f"Assumption bounds on {case.name}"
        assert faith_by_sys["Faithful-LengthMatched"][-1] == 1.0, f"LM failed on {case.name}"
        assert faith_by_sys["Faithful-Concise"][-1] == 1.0, f"Concise failed on {case.name}"
        assert bp_by_sys["Faithful-LengthMatched"][-1] == 1.0

        distinct_bleu_vectors.add(tuple(vec_b4))
        distinct_pgeo_vectors.add(tuple(vec_pg))

        if max(fn_lm4, key=lambda t: t[1])[3] == 1.0:
            bleu_top1_faithful_lm4 += 1
        if max(fn_lm4, key=lambda t: t[2])[3] == 1.0:
            pgeo_top1_faithful_lm4 += 1
        if max(fn_all5, key=lambda t: t[1])[3] == 1.0:
            bleu_top1_faithful_all5 += 1
        if max(fn_lm4, key=lambda t: t[3])[3] == 1.0:
            ast_top1_faithful_lm4 += 1

    # Non-cloning invariant: all 12 items produce 12 distinct score vectors and contracts!
    assert len(distinct_contracts) == 12
    assert len(distinct_bleu_vectors) == 12
    assert len(distinct_pgeo_vectors) == 12

    mean_bleu = {k: sum(v) / len(v) for k, v in bleu_by_sys.items()}
    mean_pgeo = {k: sum(v) / len(v) for k, v in pgeo_by_sys.items()}
    mean_bp = {k: sum(v) / len(v) for k, v in bp_by_sys.items()}
    mean_faith = {k: sum(v) / len(v) for k, v in faith_by_sys.items()}

    # Pure surface-copy inversion at BP = 1.0 (zero brevity penalty!)
    lm_bleu_ratio = mean_bleu["Stale-Copy"] / mean_bleu["Faithful-LengthMatched"]
    lm_pgeo_ratio = mean_pgeo["Stale-Copy"] / mean_pgeo["Faithful-LengthMatched"]
    # Concise rewrite decomposition: BLEU-4 inversion vs BP=1.0 P_geo inversion
    concise_pgeo_ratio = mean_pgeo["Stale-Copy"] / mean_pgeo["Faithful-Concise"]
    concise_bleu_ratio = mean_bleu["Stale-Copy"] / mean_bleu["Faithful-Concise"]

    rho_lm4_bleu = _spearman_rho(lm4_bleus, lm4_faiths)
    rho_lm4_pgeo = _spearman_rho(lm4_pgeos, lm4_faiths)
    rho_all5_bleu = _spearman_rho(all5_bleus, all5_faiths)
    rho_all5_pgeo = _spearman_rho(all5_pgeos, all5_faiths)

    assert mean_faith["Stale-Copy"] == 0.0
    assert mean_faith["Faithful-LengthMatched"] == 1.0
    assert mean_faith["Faithful-Concise"] == 1.0
    assert mean_bp["Faithful-LengthMatched"] == 1.0
    assert lm_bleu_ratio > 5.0 and lm_pgeo_ratio > 5.0
    assert concise_pgeo_ratio > 2.5 and concise_bleu_ratio > concise_pgeo_ratio
    assert rho_lm4_bleu < -0.50 and rho_lm4_pgeo < -0.50
    assert rho_all5_bleu < -0.50 and rho_all5_pgeo < -0.50
    assert bleu_top1_faithful_lm4 == 0 and pgeo_top1_faithful_lm4 == 0
    assert bleu_top1_faithful_all5 == 0 and ast_top1_faithful_lm4 == 12

    print("PROBE 5 [Basis: derived + execution (12 distinct AST contracts, N_eff=12)]")
    print(
        f"  Length-matched BP=1.0 comparison (12 distinct vectors, 48 candidates):"
        f" Stale-Copy BLEU-4={mean_bleu['Stale-Copy']:.3f} (P_geo={mean_pgeo['Stale-Copy']:.3f},"
        f" BP={mean_bp['Stale-Copy']:.3f}, faith=0.0%) vs Faithful-LengthMatched"
        f" BLEU-4={mean_bleu['Faithful-LengthMatched']:.3f}"
        f" (P_geo={mean_pgeo['Faithful-LengthMatched']:.3f}, BP=1.000, faith=100.0%)"
        f" -> {lm_bleu_ratio:.2f}x BLEU-4 / {lm_pgeo_ratio:.2f}x P_geo inversion"
    )
    print(
        f"  Concise rewrite BP decomposition (Faithful-Concise, faith=100.0%):"
        f" BP=1.0 P_geo={mean_pgeo['Faithful-Concise']:.3f} ({concise_pgeo_ratio:.2f}x below Stale-Copy),"
        f" mean BP={mean_bp['Faithful-Concise']:.3f} -> standard BLEU-4={mean_bleu['Faithful-Concise']:.3f}"
        f" ({concise_bleu_ratio:.2f}x total inversion)"
    )
    print(
        f"  Rank correlation & Top-1 faithful selection:"
        f" BP=1.0 pool rho(BLEU-4,faith)={rho_lm4_bleu:.3f}, rho(P_geo,faith)={rho_lm4_pgeo:.3f};"
        f" 5-cand pool rho(BLEU-4,faith)={rho_all5_bleu:.3f}, rho(P_geo,faith)={rho_all5_pgeo:.3f};"
        f" Top-1 faithful: BLEU-4=0/12 (0.0%), P_geo=0/12 (0.0%), AST-Verifier=12/12 (100.0%)"
    )
    return {
        "n_distinct_vectors": len(distinct_bleu_vectors),
        "lm_bleu_ratio": lm_bleu_ratio,
        "lm_pgeo_ratio": lm_pgeo_ratio,
        "concise_pgeo_ratio": concise_pgeo_ratio,
        "concise_bleu_ratio": concise_bleu_ratio,
        "rho_lm4_bleu": rho_lm4_bleu,
        "rho_lm4_pgeo": rho_lm4_pgeo,
        "rho_all5_bleu": rho_all5_bleu,
        "rho_all5_pgeo": rho_all5_pgeo,
    }


def main() -> int:
    if sys.version_info < (3, 10):
        raise SystemExit("Python 3.10+ required")
    _verify_bleu_reference_vectors()
    print("=========================================================================")
    print("CODE DOCUMENTATION, REPO ONBOARDING & DOCTEST ORACLE VERIFICATION SUITE")
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
    print("ALL 5 DOCUMENTATION, ONBOARDING & DOCTEST PROBES PASSED INVARIANTS.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
