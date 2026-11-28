# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Deterministic defender-side Tier-1 bucketing.

Keeps Tier-1 fingerprinting intentionally straightforward and maintainable by
deriving `RT-<KIND>-<12hex>` (and `RT-ESC-<12hex>` on sandbox escapes) directly
from already-structured defender outputs rather than AST/MIR alpha-renamers or
custom source lexers. Downstream semantic clustering uses the receipt's
`trace_artifacts` payload.
"""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any


_KIND_PREFIX = {
    "PROOF_HACK": "PH",
    "CODE_AND_PROOF_HACK": "CPH",
    "SPEC_PREFLIGHT_HACK": "SP",
    "THEORY_AUDIT_HACK": "TA",
}

ALLOWED_STANDARD_AXIOMS = frozenset(
    {"propext", "Classical.choice", "Quot.sound"}
)

BASELINE_DEFERRED = frozenset(
    {
        "complete review-surface reporting",
        "source-to-deployed-binary correspondence",
    }
)


_IGNORE_WITNESS_PATHS = frozenset({"manifest.json", "incorrectness/claim.md"})

_WS_RUN_RE = re.compile(r"\s+")
_HEX_CHARS = frozenset("0123456789abcdefABCDEF")


def _is_word_char(ch: str) -> bool:
    return ("A" <= ch <= "Z") or ("a" <= ch <= "z") or ("0" <= ch <= "9") or ch == "_"


def _build_raw_quote_index(text: str) -> tuple[list[int], list[int], list[int]]:
    """Index `"` positions, trailing `#` run lengths, and suffix maxes once."""
    n = len(text)
    positions: list[int] = []
    hashes: list[int] = []
    cur = 0
    while True:
        q = text.find('"', cur)
        if q < 0:
            break
        k = q + 1
        while k < n and text[k] == "#":
            k += 1
        positions.append(q)
        hashes.append(k - (q + 1))
        cur = k
    m = len(positions)
    suf_max = [0] * m
    best = -1
    for idx in range(m - 1, -1, -1):
        if hashes[idx] > best:
            best = hashes[idx]
        suf_max[idx] = best
    return positions, hashes, suf_max


def _match_char_literal(text: str, quote_pos: int, n: int) -> int | None:
    """Return end index of a Rust/byte char literal starting at `quote_pos`."""
    k = quote_pos + 1
    if k >= n or text[k] == "\n":
        return None
    if text[k] != "\\":
        if text[k] == "'" or k + 1 >= n or text[k + 1] != "'":
            return None
        return k + 2
    esc = k + 1
    if esc >= n or text[esc] == "\n":
        return None
    if text[esc] == "x" and esc + 2 < n:
        if text[esc + 1] in _HEX_CHARS and text[esc + 2] in _HEX_CHARS:
            if esc + 3 < n and text[esc + 3] == "'":
                return esc + 4
    if text[esc] == "u" and esc + 1 < n and text[esc + 1] == "{":
        p = esc + 2
        while p < n and (text[p] in _HEX_CHARS or text[p] == "_"):
            p += 1
        if p > esc + 2 and p + 1 < n and text[p] == "}" and text[p + 1] == "'":
            return p + 2
    if esc + 1 < n and text[esc + 1] == "'":
        return esc + 2
    return None


def _normalize_witness_text(text: str) -> str:
    """Collapse whitespace in O(n) while keeping literals verbatim."""
    n = len(text)
    out: list[str] = []
    plain_start = 0
    pos = 0
    no_c_block_close = False
    no_lean_block_close = False
    no_plain_quote_close = False
    no_guillemet_close = False
    raw_index: tuple[list[int], list[int], list[int]] | None = None
    raw_cursor = 0

    def flush_plain(end: int) -> None:
        if end > plain_start:
            out.append(_WS_RUN_RE.sub(" ", text[plain_start:end]))

    while pos < n:
        ch = text[pos]
        if ch == "/":
            if pos + 1 < n:
                nxt = text[pos + 1]
                if nxt == "/":
                    nl = text.find("\n", pos + 2)
                    end = n if nl < 0 else nl
                    flush_plain(pos)
                    out.append(_WS_RUN_RE.sub(" ", text[pos:end]))
                    pos = end
                    plain_start = pos
                    continue
                if nxt == "*" and not no_c_block_close:
                    close = text.find("*/", pos + 2)
                    if close < 0:
                        no_c_block_close = True
                    else:
                        flush_plain(pos)
                        out.append(_WS_RUN_RE.sub(" ", text[pos : close + 2]))
                        pos = close + 2
                        plain_start = pos
                        continue
                if nxt == "-" and not no_lean_block_close:
                    close = text.find("-/", pos + 2)
                    if close < 0:
                        no_lean_block_close = True
                    else:
                        flush_plain(pos)
                        out.append(_WS_RUN_RE.sub(" ", text[pos : close + 2]))
                        pos = close + 2
                        plain_start = pos
                        continue
            pos += 1
            continue

        if ch == "-" and pos + 1 < n and text[pos + 1] == "-":
            nl = text.find("\n", pos + 2)
            end = n if nl < 0 else nl
            flush_plain(pos)
            out.append(_WS_RUN_RE.sub(" ", text[pos:end]))
            pos = end
            plain_start = pos
            continue

        if ch == "«" and not no_guillemet_close:
            close = text.find("»", pos + 1)
            if close < 0:
                no_guillemet_close = True
                pos += 1
            else:
                flush_plain(pos)
                out.append(text[pos : close + 1])
                pos = close + 1
                plain_start = pos
            continue

        prev_is_word = pos > 0 and _is_word_char(text[pos - 1])

        # Try `(?:b|c)?r#*"..."#*` raw string literal in O(n) amortized time.
        if not prev_is_word and (
            ch == "r"
            or (ch in ("b", "c") and pos + 1 < n and text[pos + 1] == "r")
        ):
            r_idx = pos if ch == "r" else pos + 1
            k = r_idx + 1
            while k < n and text[k] == "#":
                k += 1
            if k < n and text[k] == '"':
                hashes_needed = k - (r_idx + 1)
                if raw_index is None:
                    raw_index = _build_raw_quote_index(text)
                q_pos, q_hashes, q_suf = raw_index
                content_start = k + 1
                m = len(q_pos)
                while raw_cursor < m and q_pos[raw_cursor] < content_start:
                    raw_cursor += 1
                if raw_cursor < m and q_suf[raw_cursor] >= hashes_needed:
                    j = raw_cursor
                    while q_hashes[j] < hashes_needed:
                        j += 1
                    end = q_pos[j] + 1 + hashes_needed
                    flush_plain(pos)
                    out.append(text[pos:end])
                    pos = end
                    plain_start = pos
                    raw_cursor = j + 1
                    continue
                pos += 1
                continue

        # Try plain / prefixed string literal `(?:b|c)?"..."`.
        if not prev_is_word and not no_plain_quote_close and (
            ch == '"'
            or (ch in ("b", "c") and pos + 1 < n and text[pos + 1] == '"')
        ):
            q_open = pos if ch == '"' else pos + 1
            k = q_open + 1
            matched_end: int | None = None
            while k < n:
                ck = text[k]
                if ck == "\\":
                    k += 2
                elif ck == '"':
                    matched_end = k + 1
                    break
                else:
                    k += 1
            if matched_end is not None:
                flush_plain(pos)
                out.append(text[pos:matched_end])
                pos = matched_end
                plain_start = pos
                continue
            # Forward scan hit EOF without an unescaped closing quote.
            no_plain_quote_close = True
            pos += 1
            continue

        # Try char / byte char literal `(?<![A-Za-z0-9_'])b?'...'`.
        if not prev_is_word and (pos == 0 or text[pos - 1] != "'"):
            if ch == "'" or (ch == "b" and pos + 1 < n and text[pos + 1] == "'"):
                q_open = pos if ch == "'" else pos + 1
                char_end = _match_char_literal(text, q_open, n)
                if char_end is not None:
                    flush_plain(pos)
                    out.append(text[pos:char_end])
                    pos = char_end
                    plain_start = pos
                    continue

        pos += 1

    flush_plain(n)
    return "".join(out).strip()


def compute_witness_hash(submission_files: dict[str, bytes]) -> str:
    """Compute SHA-256 over literal-preserving normalized code/proof files.

    Advisory `manifest.json` and E2 English prose (`incorrectness/claim.md`)
    are intentionally excluded so prose never perturbs `dedup` fingerprints.
    String/char/raw-string/guillemet literals remain exact verbatim bytes.
    """
    parts: list[str] = []
    for relpath in sorted(submission_files):
        if relpath in _IGNORE_WITNESS_PATHS:
            continue
        text = submission_files[relpath].decode("utf-8", errors="replace")
        normalized = _normalize_witness_text(text)
        parts.append(f"{relpath}:{normalized}")
    blob = "\n".join(parts).encode("utf-8")
    return hashlib.sha256(blob).hexdigest()


def _str_list(obj: dict[str, Any], key: str) -> list[str]:
    val = obj.get(key)
    return [x for x in val if isinstance(x, str)] if isinstance(val, list) else []


def extract_receipt_anomalies(
    receipt: dict[str, Any] | None,
    *,
    inspect_report: dict[str, Any] | None = None,
    allowed_axioms: frozenset[str] = ALLOWED_STANDARD_AXIOMS,
) -> list[str]:
    """Extract sorted defender-observed Receipt v3, audit, and inspect tags."""
    anomalies: set[str] = set()
    if isinstance(receipt, dict):
        sandbox = receipt.get("elaboration_sandbox")
        if sandbox == "none":
            anomalies.add("sandbox:none")
        audit = receipt.get("audit")
        if isinstance(audit, dict):
            for ax in _str_list(audit, "axioms"):
                if ax not in allowed_axioms:
                    anomalies.add(f"unexpected_axiom:{ax}")
            if audit.get("sorryDeclarations"):
                anomalies.add("audit:sorry_declared")
        for ax in _str_list(receipt, "axioms"):
            if ax not in allowed_axioms:
                anomalies.add(f"unexpected_axiom:{ax}")
        if receipt.get("sorryDeclarations"):
            anomalies.add("audit:sorry_declared")
        for taint in _str_list(receipt, "taint_reasons"):
            anomalies.add(f"taint:{taint}")
        for def_item in _str_list(receipt, "deferred"):
            if def_item not in BASELINE_DEFERRED:
                anomalies.add(f"deferred:{def_item}")
    if isinstance(inspect_report, dict):
        for key in (
            "policy_violations",
            "invariant_violations",
            "unrecognized_fields",
        ):
            for entry in _str_list(inspect_report, key):
                anomalies.add(f"inspect:{key}:{entry}")
    return sorted(anomalies)


_MIRI_UB_HEAD_RE = re.compile(
    r"^error(?:\[[^\]]+\])?: Undefined Behavior:"
)
_CARGO_DIAG_STOP_RE = re.compile(
    r"^(?:error(?:\[[^\]]+\])?:|warning(?:\[[^\]]+\])?:|"
    r"note: (?:some details|run with)|aborting due to)"
)
_SOURCE_QUOTE_RE = re.compile(r"^\s*(?:\d+\s*|\.\.\.\s*)?\|")
_LOCATION_ARROW_RE = re.compile(r"^\s*--> ")


def extract_miri_ub_diagnostic(output: str) -> str:
    """Return Miri's UB headline and help text without warnings or source quotes."""
    lines = output.splitlines()
    start_idx: int | None = None
    for idx, line in enumerate(lines):
        if _MIRI_UB_HEAD_RE.match(line):
            start_idx = idx
            break
    if start_idx is None:
        return "\n".join(
            line
            for line in lines
            if not _SOURCE_QUOTE_RE.match(line)
            and not _LOCATION_ARROW_RE.match(line)
        )

    kept: list[str] = [lines[start_idx]]
    in_header = True
    in_backtrace = False
    for line in lines[start_idx + 1 :]:
        if _CARGO_DIAG_STOP_RE.match(line):
            break
        stripped = line.strip()
        if _SOURCE_QUOTE_RE.match(line) or _LOCATION_ARROW_RE.match(line):
            in_header = False
            continue
        if stripped.startswith("help:") and "was allocated here:" in stripped:
            in_header = False
            in_backtrace = False
            continue
        if stripped.startswith("= note: stack backtrace:"):
            in_header = False
            in_backtrace = True
            continue
        if in_backtrace:
            if not stripped or stripped.startswith("="):
                in_backtrace = False
            else:
                continue
        if in_header:
            if stripped:
                kept.append(line)
            else:
                in_header = False
        elif stripped.startswith("= help:"):
            kept.append(line)
    return "\n".join(kept)


def classify_miri_ub(output: str) -> str:
    """Map Miri UB diagnostic text to a normalized `UbFaultClass` tag."""
    lower = extract_miri_ub_diagnostic(output).lower()
    if "stacked borrows" in lower or "tree borrows" in lower:
        return "ub:tree_borrows"
    if "uninitialized" in lower or "using uninitialized data" in lower:
        return "ub:uninitialized"
    if (
        "out-of-bounds" in lower
        or "dereferencing pointer failed" in lower
        or "in-bounds pointer arithmetic failed" in lower
        or "memory access failed" in lower
    ):
        if "dangling" in lower or ("alloc" in lower and "freed" in lower):
            return "ub:dangling_pointer"
        return "ub:out_of_bounds"
    if "dangling" in lower or "use after free" in lower:
        return "ub:dangling_pointer"
    if "unchecked_" in lower or "overflow" in lower or "unreachable" in lower:
        if "unreachable" in lower and "unchecked_" not in lower:
            return "ub:unreachable"
        return "ub:arithmetic_overflow"
    if "aliasing" in lower or "reborrow" in lower:
        return "ub:aliasing"
    if "alignment" in lower or "misaligned" in lower:
        return "ub:misaligned"
    return "ub:other"


def compute_dedup_metadata(
    *,
    scenario_id: str,
    scenario_kind: str,
    submission_files: dict[str, bytes],
    receipt: dict[str, Any] | None = None,
    inspect_report: dict[str, Any] | None = None,
    oracle_fault_class: str | None = None,
    incorrectness_evidence_tier: str | None = None,
    sandbox_escape_detected: bool = False,
    tampered_paths: list[str] | tuple[str, ...] = (),
    ast_disallowed_tags: list[str] | tuple[str, ...] = (),
) -> dict[str, Any]:
    """Compute defender-only `dedup` object for an exploit or review receipt."""
    receipt_anomalies = extract_receipt_anomalies(
        receipt, inspect_report=inspect_report
    )
    witness_hash = compute_witness_hash(submission_files)

    if sandbox_escape_detected:
        tampered = sorted(set(tampered_paths))
        payload: dict[str, Any] = {
            "kind": scenario_kind,
            "check_or_fault": "sandbox_escape",
            "tampered_paths": tampered,
            "receipt_anomalies": receipt_anomalies,
        }
        features = ["mechanism:sandbox_escape", f"check:{scenario_id}"]
        features.extend(f"tampered:{p}" for p in tampered)
        features.extend(receipt_anomalies)
        kind_code = "ESC"
        summary = (
            f"sandbox_escape in {scenario_kind} ({scenario_id}); "
            f"tampered={','.join(tampered) or 'unknown'}"
        )
    else:
        tier_tag = (
            incorrectness_evidence_tier
            if incorrectness_evidence_tier in ("lean_patch_proof", "prose_claim")
            else None
        )
        ast_tags = sorted(
            {t for t in ast_disallowed_tags if isinstance(t, str) and t}
        )
        check_or_fault = oracle_fault_class or tier_tag or scenario_id
        payload = {
            "kind": scenario_kind,
            "check_or_fault": check_or_fault,
            "receipt_anomalies": receipt_anomalies,
        }
        if ast_tags:
            payload["ast_disallowed_tags"] = ast_tags
        kind_code = _KIND_PREFIX.get(scenario_kind, "UNK")
        features = [f"check:{scenario_id}"]
        if oracle_fault_class:
            features.append(f"fault:{oracle_fault_class}")
        if tier_tag:
            features.append(f"tier:{tier_tag}")
        features.extend(receipt_anomalies)
        features.extend(f"ast:{tag}" for tag in ast_tags)
        summary = (
            f"{scenario_kind} ({check_or_fault}); "
            f"anomalies={','.join(receipt_anomalies) or 'none'}"
            + (f"; ast={','.join(ast_tags)}" if ast_tags else "")
        )

    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    digest12 = hashlib.sha256(canonical.encode("utf-8")).hexdigest()[:12]
    return {
        "bug_id": f"RT-{kind_code}-{digest12}",
        "witness_hash": witness_hash,
        "mechanism_summary": summary,
        "features": sorted(set(features)),
    }
