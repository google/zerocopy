# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Fast PR gate asserting TrustedBoundary claim sync with Rust audit fixtures."""

from pathlib import Path
import re
import tempfile
import unittest

from test_lean_template_hygiene import strip_lean_comments_and_strings


REPO_ROOT = Path(__file__).resolve().parents[2]
TRUSTED_BOUNDARY = REPO_ROOT / "anneal" / "trusted" / "audit" / "TrustedBoundary.lean"
INSTALLED_SMOKE = (
    REPO_ROOT / "anneal" / "tests" / "cargo-anneal" / "tests" / "installed_smoke.rs"
)
BOUNDARY_AUDIT = (
    REPO_ROOT / "anneal" / "tests" / "audit" / "tests" / "boundary_audit.rs"
)
MIR_WP_FIXTURE = (
    REPO_ROOT / "anneal" / "tests" / "testkit" / "src" / "mir_wp_fixture.rs"
)

# Meta-claim helper bindings referenced inside `reqConsts` lists rather than
# standalone theorem obligations in `verifyMirWpCoreTheorems`.
HELPER_META_CLAIMS = frozenset({"PositiveCanaryClaim", "NegativeCanaryClaim"})

# Direct `requireClaimProof env locals semMod wpMod` calls referencing
# `Trusted.MirSemantics.<Claim>` and `<Proof>`.
_DIRECT_CLAIM_RE = re.compile(
    r"\brequireClaimProof\s+\S+\s+\S+\s+\S+\s+\S+\s+"
    r"`Trusted\.MirSemantics\.([A-Za-z0-9_]+)\s+"
    r"(?:none|\(some\s+`[A-Za-z0-9_.]+\))\s+"
    r"`([A-Za-z0-9_.]+)",
    re.DOTALL,
)

# Tuple entries in `for (claimName, proofName, reqConsts) in [...]`
_TUPLE_CLAIM_RE = re.compile(
    r"\(\s*`Trusted\.MirSemantics\.([A-Za-z0-9_]+)\s*,\s*`([A-Za-z0-9_.]+)\s*,",
    re.DOTALL,
)

_ANY_SEM_CLAIM_RE = re.compile(r"`Trusted\.MirSemantics\.([A-Za-z0-9_]*Claim[A-Za-z0-9_]*)")


def _match_rust_comment_or_literal(
    source: str, i: int
) -> tuple[str, int] | None:
    """Match a Rust comment, raw string, normal string, or char literal at `i`.

    Returns `(kind, end_idx)` where `kind` is `"comment"` or `"literal"`, or
    `None` if `source[i:]` starts ordinary Rust code (including lifetimes such
    as `'static`).
    """
    n = len(source)
    ch = source[i]
    nxt = source[i + 1] if i + 1 < n else ""

    # Line comment: `// ...`
    if ch == "/" and nxt == "/":
        j = i + 2
        while j < n and source[j] != "\n":
            j += 1
        return "comment", j

    # Nested block comment: `/* ... */`
    if ch == "/" and nxt == "*":
        depth = 1
        j = i + 2
        while j < n and depth > 0:
            if source[j] == "/" and j + 1 < n and source[j + 1] == "*":
                depth += 1
                j += 2
            elif source[j] == "*" and j + 1 < n and source[j + 1] == "/":
                depth -= 1
                j += 2
            else:
                j += 1
        return "comment", j

    prev_is_ident = i > 0 and (source[i - 1].isalnum() or source[i - 1] == "_")

    # Raw string literal: `r#"..."#`, `br#"..."#`, `cr#"..."#`
    if not prev_is_ident and ch in ("r", "b", "c"):
        j = i + (1 if ch in ("b", "c") and nxt == "r" else 0)
        if j < n and source[j] == "r":
            k = j + 1
            hashes = 0
            while k < n and source[k] == "#":
                hashes += 1
                k += 1
            if k < n and source[k] == '"':
                closing = '"' + ("#" * hashes)
                end_idx = source.find(closing, k + 1)
                return "literal", (n if end_idx == -1 else end_idx + len(closing))

    # Normal, byte, or C string literal: `"..."`, `b"..."`, `c"..."`
    str_quote = -1
    if ch == '"':
        str_quote = i
    elif not prev_is_ident and ch in ("b", "c") and nxt == '"':
        str_quote = i + 1
    if str_quote != -1:
        j = str_quote + 1
        while j < n:
            if source[j] == "\\" and j + 1 < n:
                j += 2
            elif source[j] == '"':
                return "literal", j + 1
            else:
                j += 1
        return "literal", n

    # Char or byte-char literal: `'a'`, `'\''`, `'"'`, `'}'`, `b'"'`
    # (Lifetimes like `'static` are not closed by `'` after 1 char/escape.)
    char_quote = -1
    if ch == "'" and not prev_is_ident:
        char_quote = i
    elif not prev_is_ident and ch == "b" and nxt == "'":
        char_quote = i + 1
    if char_quote != -1:
        j = char_quote + 1
        if j < n and source[j] == "\\" and j + 1 < n:
            k = j + 2
            while k < n and source[k] not in ("'", "\n"):
                k += 1
            if k < n and source[k] == "'":
                return "literal", k + 1
        elif j + 1 < n and source[j] not in ("'", "\n") and source[j + 1] == "'":
            return "literal", j + 2

    return None


def _blank_preserving_newlines(text: str) -> str:
    return "".join("\n" if c == "\n" else " " for c in text)


def _strip_rust_comments(source: str) -> str:
    """Strip Rust `//` and nested `/* ... */` comments outside literals."""
    out: list[str] = []
    n = len(source)
    i = 0
    while i < n:
        tok = _match_rust_comment_or_literal(source, i)
        if tok is not None:
            kind, end_idx = tok
            segment = source[i:end_idx]
            out.append(
                _blank_preserving_newlines(segment)
                if kind == "comment"
                else segment
            )
            i = end_idx
            continue
        out.append(source[i])
        i += 1
    return "".join(out)


def _strip_rust_comments_and_strings(source: str) -> str:
    """Strip Rust comments, strings, raw strings, and char literals."""
    out: list[str] = []
    n = len(source)
    i = 0
    while i < n:
        tok = _match_rust_comment_or_literal(source, i)
        if tok is not None:
            _, end_idx = tok
            out.append(_blank_preserving_newlines(source[i:end_idx]))
            i = end_idx
            continue
        out.append(source[i])
        i += 1
    return "".join(out)


def extract_verify_mir_wp_body(trusted_boundary_src: str) -> str:
    """Extract the body of `def verifyMirWpCoreTheorems` from `TrustedBoundary.lean`."""
    stripped = strip_lean_comments_and_strings(trusted_boundary_src)
    match = re.search(r"^def\s+verifyMirWpCoreTheorems\b", stripped, re.MULTILINE)
    if not match:
        raise AssertionError("Could not find `def verifyMirWpCoreTheorems` in TrustedBoundary.lean")

    start = match.start()
    rest = stripped[match.end() :]
    # Find the next top-level (column 0) Lean declaration.
    next_decl = re.search(
        r"\n(?:(?:private|protected|partial|noncomputable|unsafe)\s+)*"
        r"(?:def|theorem|inductive|structure|abbrev|namespace|end|class|instance)\b",
        rest,
    )
    end = match.end() + next_decl.start() if next_decl else len(stripped)
    return stripped[start:end]


def parse_required_mir_wp_claims(trusted_boundary_src: str) -> dict[str, str]:
    """Return `{claim_name: proof_short_name}` required by `verifyMirWpCoreTheorems`."""
    body = extract_verify_mir_wp_body(trusted_boundary_src)
    claims: dict[str, str] = {}

    for match in _DIRECT_CLAIM_RE.finditer(body):
        claim_name = match.group(1)
        proof_short = match.group(2).rsplit(".", 1)[-1]
        claims[claim_name] = proof_short

    for match in _TUPLE_CLAIM_RE.finditer(body):
        claim_name = match.group(1)
        proof_short = match.group(2).rsplit(".", 1)[-1]
        claims[claim_name] = proof_short

    # Fail closed if a new `*Claim*` declaration appears in
    # `verifyMirWpCoreTheorems` in a syntactic shape neither regex recognized.
    all_sem_claims = set(_ANY_SEM_CLAIM_RE.findall(body)) - HELPER_META_CLAIMS
    unparsed = sorted(all_sem_claims - set(claims))
    if unparsed:
        raise AssertionError(
            "Unrecognized claim references in verifyMirWpCoreTheorems "
            f"(update parser in test_trusted_boundary_claim_sync.py): {unparsed}"
        )

    if not claims:
        raise AssertionError("Parsed zero claims from verifyMirWpCoreTheorems")

    return claims


def _extract_balanced_delim_block(
    source: str, start_idx: int, open_ch: str, close_ch: str
) -> str:
    """Extract a balanced `open_ch ... close_ch` block skipping Rust literals/comments."""
    open_pos = source.find(open_ch, start_idx)
    if open_pos == -1:
        return ""
    depth = 0
    n = len(source)
    i = open_pos
    while i < n:
        tok = _match_rust_comment_or_literal(source, i)
        if tok is not None:
            i = tok[1]
            continue
        ch = source[i]
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return source[open_pos : i + 1]
        i += 1
    return source[open_pos:]


def _extract_brace_block(source: str, start_idx: int) -> str:
    """Extract a balanced `{ ... }` block starting at or after `start_idx`."""
    return _extract_balanced_delim_block(source, start_idx, "{", "}")


def _extract_bracket_block(source: str, start_idx: int) -> str:
    """Extract a balanced `[ ... ]` block starting at or after `start_idx`."""
    return _extract_balanced_delim_block(source, start_idx, "[", "]")


def _extract_claims_and_pairs_from_rust_region(
    region: str,
) -> tuple[set[str], set[tuple[str, str]]]:
    """Extract defined MirWp claims and exact `(claim, proof)` pairs from Rust fixture code."""
    # Collapse Rust string line continuations (`\` + newline + whitespace) and
    # expand escaped `\n` newlines so multiline Rust string literals such as
    # `...True\n\ def WpSoundnessClaim...` have clean word boundaries before
    # `def` and `theorem`.
    normalized = re.sub(r"\\\r?\n[ \t]*", "", region).replace("\\n", "\n")

    defined_claims: set[str] = set()
    pairs: set[tuple[str, str]] = set()

    # 1. Explicit Lean `def <Name>` declarations inside Rust string literals.
    for match in re.finditer(r"\bdef\s+([A-Za-z0-9_]*Claim[A-Za-z0-9_]*)\b", normalized):
        name = match.group(1)
        if name not in HELPER_META_CLAIMS:
            defined_claims.add(name)

    # 2. Explicit Lean `theorem <Proof> : Trusted.MirSemantics.<Claim>`
    #    declarations.
    for match in re.finditer(
        r"\btheorem\s+([A-Za-z0-9_]+)\s*:\s*Trusted\.MirSemantics\.([A-Za-z0-9_]+)",
        normalized,
    ):
        proof_name = match.group(1)
        claim_name = match.group(2)
        pairs.add((claim_name, proof_name))

    # 3. Tuple-style claim entries:
    #    - 3-tuples `(claim, wp_param, proof)` such as `CORE_WP_CLAIMS` in
    #      `mir_wp_fixture.rs`:
    #      `("WpSoundnessClaim", "wpProg", "wellFormed_...")`
    #    - 2-tuples `(claim, proof)` or 4-tuples `(claim, proof, body, term)`
    #      such as `SYNTHETIC_CANARIES` / `let canaries`:
    #      `("Canary...Claim", "canary_...", ...)`
    for match in re.finditer(
        r'\(\s*"([A-Za-z0-9_]*Claim[A-Za-z0-9_]*)"\s*,\s*"([A-Za-z0-9_]+)"'
        r'(?:\s*,\s*"([A-Za-z0-9_]+)"\s*,?\s*\))?',
        normalized,
    ):
        claim_name = match.group(1)
        proof_name = (
            match.group(3) if match.group(3) is not None else match.group(2)
        )
        defined_claims.add(claim_name)
        pairs.add((claim_name, proof_name))

    # 4. Struct-style canary entries (future-proof for `mir_wp_fixture.rs`):
    #    `{ ... claim: "Canary...Claim", ... proof: "canary_..." ... }`
    #    (either field order).
    for match in re.finditer(r"\{[^{}]*\}", normalized):
        struct_body = match.group(0)
        claim_m = re.search(
            r'\bclaim\s*:\s*"([A-Za-z0-9_]*Claim[A-Za-z0-9_]*)"', struct_body
        )
        proof_m = re.search(r'\bproof\s*:\s*"([A-Za-z0-9_]+)"', struct_body)
        if claim_m and proof_m:
            defined_claims.add(claim_m.group(1))
            pairs.add((claim_m.group(1), proof_m.group(1)))

    return defined_claims, pairs


def _delegates_to_mir_wp_fixture(rust_src: str, shared_fixture_path: Path) -> bool:
    """Return True iff `rust_src` actively references `mir_wp_fixture::...` outside `use` items."""
    if not shared_fixture_path.is_file():
        return False
    code = _strip_rust_comments_and_strings(rust_src)
    # Strip `use ...;` statements so a bare unused
    # `use anneal_testkit::mir_wp_fixture;` cannot trigger delegation without
    # an actual symbol/call reference.
    non_use_code = re.sub(r"\buse\s+[^;]+;", " ", code)
    if re.search(r"\bmir_wp_fixture::[A-Za-z0-9_]+\b", non_use_code):
        return True

    # Also allow explicit imported symbols from `mir_wp_fixture::{...}` /
    # `mir_wp_fixture::Sym` ONLY if at least one imported symbol is actually
    # referenced outside `use` statements.
    imported_syms: set[str] = set()
    for match in re.finditer(r"\buse\s+[^;]*\bmir_wp_fixture::([^;]+);", code):
        tail = match.group(1).strip()
        if tail.startswith("{") and tail.endswith("}"):
            entries = tail[1:-1].split(",")
        else:
            entries = [tail]
        for entry in entries:
            part = entry.strip()
            if not part or part == "*" or part == "self":
                continue
            as_match = re.match(r"^[A-Za-z0-9_:]+\s+as\s+([A-Za-z0-9_]+)$", part)
            if as_match:
                imported_syms.add(as_match.group(1))
            elif re.match(r"^[A-Za-z0-9_]+$", part):
                imported_syms.add(part)

    return any(
        re.search(rf"\b{re.escape(sym)}\b", non_use_code) for sym in imported_syms
    )


def _extract_inline_mir_wp_regions(code: str) -> list[str]:
    """Return inline `SYNTHETIC_CANARIES` / `MirWpSyntheticSpec` / `let canaries` regions."""
    regions: list[str] = []
    synth_canaries = re.search(r"\bconst\s+SYNTHETIC_CANARIES\b", code)
    if synth_canaries:
        eq_idx = code.find("=", synth_canaries.end())
        if eq_idx != -1:
            regions.append(_extract_bracket_block(code, eq_idx))
    spec_valid = re.search(r"\bimpl\s+MirWpSyntheticSpec\b", code)
    if spec_valid:
        impl_block = _extract_brace_block(code, spec_valid.end())
        valid_fn = re.search(r"\bfn\s+valid\s*\(", impl_block)
        if valid_fn:
            regions.append(_extract_brace_block(impl_block, valid_fn.end()))
        else:
            regions.append(impl_block)
    local_canaries = re.search(r"\blet\s+canaries\b", code)
    if local_canaries:
        eq_idx = code.find("=", local_canaries.end())
        if eq_idx != -1:
            regions.append(_extract_bracket_block(code, eq_idx))
    return regions


def extract_fixture_claims_for_file(
    rust_file: Path,
    *,
    shared_fixture_path: Path = MIR_WP_FIXTURE,
) -> tuple[str, set[str], set[tuple[str, str]]]:
    """Extract MirWp `(label, defined_claims, claim_proof_pairs)` for a Rust test file.

    If `rust_file` actively references `anneal_testkit::mir_wp_fixture` and
    `shared_fixture_path` exists, inspects `shared_fixture_path` seamlessly and
    rejects stray partial inline MirWp claim stubs in `rust_file`.
    """
    raw = rust_file.read_text(encoding="utf-8")
    code = _strip_rust_comments(raw)
    if _delegates_to_mir_wp_fixture(raw, shared_fixture_path):
        shared_code = _strip_rust_comments(
            shared_fixture_path.read_text(encoding="utf-8")
        )
        shared_claims, shared_pairs = _extract_claims_and_pairs_from_rust_region(
            shared_code
        )
        inline_regions = _extract_inline_mir_wp_regions(code)
        if inline_regions:
            inline_claims, inline_pairs = _extract_claims_and_pairs_from_rust_region(
                "\n".join(inline_regions)
            )
            if inline_claims != shared_claims or inline_pairs != shared_pairs:
                raise AssertionError(
                    f"{rust_file.name} delegates to {shared_fixture_path.name} "
                    "but retains a diverging partial inline MirWp fixture "
                    f"(inline claims={sorted(inline_claims)}, "
                    f"shared claims={sorted(shared_claims)})"
                )
        return (
            f"{rust_file.name} -> {shared_fixture_path.name}",
            shared_claims,
            shared_pairs,
        )

    # For `boundary_audit.rs`, scope strictly to `SYNTHETIC_CANARIES` and
    # `MirWpSyntheticSpec::valid` so `Trusted.Correspondence` fixtures and
    # negative-test mutations do not pollute the MirWp claim set.
    spec_valid = re.search(r"\bimpl\s+MirWpSyntheticSpec\b", code)
    synth_canaries = re.search(r"\bconst\s+SYNTHETIC_CANARIES\b", code)
    if spec_valid or synth_canaries:
        regions = _extract_inline_mir_wp_regions(code)
        claims, pairs = _extract_claims_and_pairs_from_rust_region("\n".join(regions))
        return rust_file.name, claims, pairs

    # Default (e.g. `installed_smoke.rs` or standalone fixture file): scan the
    # entire stripped Rust source.
    claims, pairs = _extract_claims_and_pairs_from_rust_region(code)
    return rust_file.name, claims, pairs


def assert_claim_parity(
    required_claims: dict[str, str],
    fixture_label: str,
    fixture_claims: set[str],
    fixture_pairs: set[tuple[str, str]],
) -> None:
    """Assert 100% claim-definition and exact `(claim, proof)` pairing parity."""
    expected_claims = set(required_claims.keys())
    expected_pairs = set(required_claims.items())

    missing_claims = sorted(expected_claims - fixture_claims)
    extra_claims = sorted(fixture_claims - expected_claims)
    missing_pairs = sorted(expected_pairs - fixture_pairs)
    extra_pairs = sorted(fixture_pairs - expected_pairs)

    problems: list[str] = []
    if missing_claims:
        problems.append(f"missing claim definitions in {fixture_label}: {missing_claims}")
    if extra_claims:
        problems.append(f"stale/extra claim definitions in {fixture_label}: {extra_claims}")
    if missing_pairs:
        problems.append(f"missing/mismatched (claim, proof) pairs in {fixture_label}: {missing_pairs}")
    if extra_pairs:
        problems.append(f"stale/mismatched (claim, proof) pairs in {fixture_label}: {extra_pairs}")

    if problems:
        raise AssertionError(
            "TrustedBoundary.lean `verifyMirWpCoreTheorems` out of sync with "
            f"{fixture_label}:\n  " + "\n  ".join(problems)
        )


class TrustedBoundaryClaimSyncTests(unittest.TestCase):
    def test_live_installed_smoke_and_boundary_audit_match_trusted_boundary(self):
        required = parse_required_mir_wp_claims(
            TRUSTED_BOUNDARY.read_text(encoding="utf-8")
        )
        # Sanity-check baseline count: 2 core WP claims + >=25 canary claims.
        self.assertIn("WpSoundnessClaim", required)
        self.assertIn("WpFaultSoundnessClaim", required)
        self.assertGreaterEqual(len(required), 27)

        for rust_file in (INSTALLED_SMOKE, BOUNDARY_AUDIT):
            self.assertTrue(rust_file.is_file(), f"Missing Rust fixture: {rust_file}")
            label, claims, pairs = extract_fixture_claims_for_file(rust_file)
            assert_claim_parity(required, label, claims, pairs)

    def test_synthetic_missing_claim_fails_cleanly(self):
        tb_src = """
def verifyMirWpCoreTheorems (env : Environment) : IO Unit := do
  requireClaimProof env locals semMod wpMod
    `Trusted.MirSemantics.WpSoundnessClaim
    (some `Anneal.MirWp.wpProg)
    `Anneal.MirWp.wellFormed_and_spec_of_wp
    [`Trusted.MirSemantics.SatisfiesPost]
  requireClaimProof env locals semMod wpMod
    `Trusted.MirSemantics.ExecSoundnessClaimV2
    (some `Anneal.MirWp.execProgV2)
    `Anneal.MirWp.exec_soundness_v2
    [`Trusted.MirSemantics.Behavior]
  for (claimName, proofName, reqConsts) in [
      (`Trusted.MirSemantics.CanaryPositiveAddAnnealClaim,
        `Anneal.MirWp.canary_positive_add_anneal, [posClaim])] do
    requireClaimProof env locals semMod canaryMod claimName none proofName reqConsts

def audit : IO Unit := pure ()
"""
        required = parse_required_mir_wp_claims(tb_src)
        self.assertEqual(
            required,
            {
                "WpSoundnessClaim": "wellFormed_and_spec_of_wp",
                "ExecSoundnessClaimV2": "exec_soundness_v2",
                "CanaryPositiveAddAnnealClaim": "canary_positive_add_anneal",
            },
        )

        with tempfile.TemporaryDirectory(prefix="anneal-claim-sync-") as tmp:
            fixture_rs = Path(tmp) / "installed_smoke.rs"
            fixture_rs.write_text(
                'const SEM: &str = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n";\n'
                'const WP: &str = "theorem wellFormed_and_spec_of_wp : Trusted.MirSemantics.WpSoundnessClaim wpProg := True.intro\\n";\n'
                'const CANARIES: &[(&str, &str)] = &[("CanaryPositiveAddAnnealClaim", "canary_positive_add_anneal")];\n',
                encoding="utf-8",
            )
            label, claims, pairs = extract_fixture_claims_for_file(
                fixture_rs, shared_fixture_path=Path(tmp) / "nonexistent.rs"
            )
            with self.assertRaises(AssertionError) as ctx:
                assert_claim_parity(required, label, claims, pairs)
            self.assertIn("ExecSoundnessClaimV2", str(ctx.exception))
            self.assertIn("exec_soundness_v2", str(ctx.exception))

    def test_swapped_proof_pairings_fail_closed(self):
        tb_src = """
def verifyMirWpCoreTheorems (env : Environment) : IO Unit := do
  requireClaimProof env locals semMod wpMod
    `Trusted.MirSemantics.WpSoundnessClaim
    (some `Anneal.MirWp.wpProg)
    `Anneal.MirWp.wellFormed_and_spec_of_wp
    [`Trusted.MirSemantics.SatisfiesPost]
  requireClaimProof env locals semMod wpMod
    `Trusted.MirSemantics.WpFaultSoundnessClaim
    (some `Anneal.MirWp.wpFaultProg)
    `Anneal.MirWp.reaches_fault_and_exclusive_of_wpFault
    [`Trusted.MirSemantics.WellFormed]

def audit : IO Unit := pure ()
"""
        required = parse_required_mir_wp_claims(tb_src)
        with tempfile.TemporaryDirectory(prefix="anneal-claim-swap-") as tmp:
            swapped_rs = Path(tmp) / "swapped.rs"
            # Exact same claim set and proof set, but proofs are swapped.
            swapped_rs.write_text(
                'const SEM: &str = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n'
                'def WpFaultSoundnessClaim (_f : Nat) : Prop := True\\n";\n'
                'const WP: &str = "theorem reaches_fault_and_exclusive_of_wpFault : Trusted.MirSemantics.WpSoundnessClaim wpProg := True.intro\\n'
                'theorem wellFormed_and_spec_of_wp : Trusted.MirSemantics.WpFaultSoundnessClaim wpFaultProg := True.intro\\n";\n',
                encoding="utf-8",
            )
            label, claims, pairs = extract_fixture_claims_for_file(
                swapped_rs, shared_fixture_path=Path(tmp) / "nonexistent.rs"
            )
            with self.assertRaises(AssertionError) as ctx:
                assert_claim_parity(required, label, claims, pairs)
            self.assertIn("mismatched (claim, proof) pairs", str(ctx.exception))

    def test_delegation_to_shared_mir_wp_fixture_works(self):
        tb_src = """
def verifyMirWpCoreTheorems (env : Environment) : IO Unit := do
  requireClaimProof env locals semMod wpMod
    `Trusted.MirSemantics.WpSoundnessClaim
    (some `Anneal.MirWp.wpProg)
    `Anneal.MirWp.wellFormed_and_spec_of_wp
    [`Trusted.MirSemantics.SatisfiesPost]
  for (claimName, proofName, reqConsts) in [
      (`Trusted.MirSemantics.CanaryPositiveAddAnnealClaim,
        `Anneal.MirWp.canary_positive_add_anneal, [posClaim])] do
    requireClaimProof env locals semMod canaryMod claimName none proofName reqConsts

def audit : IO Unit := pure ()
"""
        required = parse_required_mir_wp_claims(tb_src)

        with tempfile.TemporaryDirectory(prefix="anneal-claim-sync-deleg-") as tmp:
            shared = Path(tmp) / "mir_wp_fixture.rs"
            shared.write_text(
                "pub struct Canary { pub claim: &'static str, pub proof: &'static str }\n"
                'pub const CANARIES: &[Canary] = &[Canary { claim: "CanaryPositiveAddAnnealClaim", proof: "canary_positive_add_anneal" }];\n'
                'pub const SEM: &str = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n";\n'
                'pub const WP: &str = "theorem wellFormed_and_spec_of_wp : Trusted.MirSemantics.WpSoundnessClaim wpProg := True.intro\\n";\n',
                encoding="utf-8",
            )
            consumer = Path(tmp) / "installed_smoke.rs"
            consumer.write_text(
                "use anneal_testkit::mir_wp_fixture;\n"
                "fn smoke() { let _ = mir_wp_fixture::MirWpFixture::valid(); }\n",
                encoding="utf-8",
            )
            label, claims, pairs = extract_fixture_claims_for_file(
                consumer, shared_fixture_path=shared
            )
            self.assertIn("mir_wp_fixture.rs", label)
            assert_claim_parity(required, label, claims, pairs)

            # A bare unused `use anneal_testkit::mir_wp_fixture;` must NOT count
            # as delegating.
            unused_import = Path(tmp) / "unused_import.rs"
            unused_import.write_text(
                "use anneal_testkit::mir_wp_fixture;\n"
                "fn smoke() {}\n",
                encoding="utf-8",
            )
            ui_label, ui_claims, ui_pairs = extract_fixture_claims_for_file(
                unused_import, shared_fixture_path=shared
            )
            self.assertEqual(ui_label, "unused_import.rs")
            with self.assertRaises(AssertionError):
                assert_claim_parity(required, ui_label, ui_claims, ui_pairs)

            # A mere comment/string mention of `mir_wp_fixture` must NOT trigger
            # delegation.
            non_delegating = Path(tmp) / "comment_only.rs"
            non_delegating.write_text(
                '// see anneal_testkit::mir_wp_fixture::MirWpFixture\n'
                'const NOTE: &str = "mir_wp_fixture::MirWpFixture";\n'
                'const SEM: &str = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n";\n',
                encoding="utf-8",
            )
            nd_label, nd_claims, _ = extract_fixture_claims_for_file(
                non_delegating, shared_fixture_path=shared
            )
            self.assertEqual(nd_label, "comment_only.rs")
            self.assertEqual(nd_claims, {"WpSoundnessClaim"})

            # Active delegation alongside a partial/diverging local inline
            # fixture must fail closed.
            partial = Path(tmp) / "partial_deleg.rs"
            partial.write_text(
                "use anneal_testkit::mir_wp_fixture;\n"
                "fn smoke() { let _ = mir_wp_fixture::MirWpFixture::valid(); }\n"
                'const SYNTHETIC_CANARIES: &[(&str, &str)] = &[("CanaryPositiveAddAnnealClaim", "canary_positive_add_anneal")];\n',
                encoding="utf-8",
            )
            with self.assertRaises(AssertionError) as ctx:
                extract_fixture_claims_for_file(partial, shared_fixture_path=shared)
            self.assertIn("diverging partial inline MirWp fixture", str(ctx.exception))

    def test_delegation_against_live_mir_wp_fixture_matches_trusted_boundary(self):
        self.assertTrue(
            MIR_WP_FIXTURE.is_file(),
            f"expected live shared fixture at {MIR_WP_FIXTURE}",
        )
        required = parse_required_mir_wp_claims(
            TRUSTED_BOUNDARY.read_text(encoding="utf-8")
        )
        with tempfile.TemporaryDirectory(prefix="anneal-claim-live-deleg-") as tmp:
            consumer = Path(tmp) / "live_delegating_consumer.rs"
            consumer.write_text(
                "use anneal_testkit::mir_wp_fixture;\n"
                "fn smoke() { let _ = mir_wp_fixture::MirWpFixture::valid(); }\n",
                encoding="utf-8",
            )
            label, claims, pairs = extract_fixture_claims_for_file(
                consumer, shared_fixture_path=MIR_WP_FIXTURE
            )
            self.assertIn("mir_wp_fixture.rs", label)
            assert_claim_parity(required, label, claims, pairs)

    def test_rust_lexer_handles_raw_strings_and_char_literals(self):
        with tempfile.TemporaryDirectory(prefix="anneal-claim-rust-lex-") as tmp:
            shared = Path(tmp) / "mir_wp_fixture.rs"
            shared.write_text(
                'pub const SEM: &str = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n";\n'
                'pub const WP: &str = "theorem wellFormed_and_spec_of_wp : '
                'Trusted.MirSemantics.WpSoundnessClaim wpProg := True.intro\\n";\n',
                encoding="utf-8",
            )
            # (a) Raw string ending in `\` (`r#"foo\"#`) followed by a `//`
            # comment containing `"` + `mir_wp_fixture::MirWpFixture` must NOT
            # trigger false delegation; (b) `'"'` char literal followed by
            # `// def FakeClaim` must strip the comment; (c) `'}'` and `']'`
            # char literals inside `SYNTHETIC_CANARIES` and `MirWpSyntheticSpec`
            # must NOT terminate balanced block extraction early.
            consumer = Path(tmp) / "boundary_audit.rs"
            consumer.write_text(
                'const RAW_END_BS: &str = r#"foo\\"#; // " mir_wp_fixture::MirWpFixture\n'
                'const C_RAW: &core::ffi::CStr = cr#"bar\\"#; // " mir_wp_fixture::Other\n'
                "const QUOTE_CH: char = '\"'; // def FakeClaim : Prop := True\n"
                "const BYTE_QUOTE: u8 = b'\"'; // def FakeByteClaim : Prop := True\n"
                "const SYNTHETIC_CANARIES: &[(&str, &str, char)] = &[\n"
                '    ("CanaryPositiveAddAnnealClaim", "canary_positive_add_anneal", \']\'),\n'
                "];\n"
                "impl MirWpSyntheticSpec {\n"
                "    fn valid() -> Self {\n"
                "        let _brace_ch: char = '}';\n"
                '        let _sem = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n";\n'
                '        let _wp = "theorem wellFormed_and_spec_of_wp : '
                'Trusted.MirSemantics.WpSoundnessClaim wpProg := True.intro\\n";\n'
                "        Self {}\n"
                "    }\n"
                "}\n",
                encoding="utf-8",
            )
            label, claims, pairs = extract_fixture_claims_for_file(
                consumer, shared_fixture_path=shared
            )
            self.assertEqual(label, "boundary_audit.rs")
            self.assertEqual(
                claims,
                {"WpSoundnessClaim", "CanaryPositiveAddAnnealClaim"},
            )
            self.assertEqual(
                pairs,
                {
                    ("WpSoundnessClaim", "wellFormed_and_spec_of_wp"),
                    ("CanaryPositiveAddAnnealClaim", "canary_positive_add_anneal"),
                },
            )

    def test_unrecognized_claim_pattern_fails_closed(self):
        tb_src = """
def verifyMirWpCoreTheorems (env : Environment) : IO Unit := do
  requireClaimProof env locals semMod wpMod
    `Trusted.MirSemantics.WpSoundnessClaim
    (some `Anneal.MirWp.wpProg)
    `Anneal.MirWp.wellFormed_and_spec_of_wp
    [`Trusted.MirSemantics.SatisfiesPost]
  customHelper `Trusted.MirSemantics.NovelUnparsedClaim

def audit : IO Unit := pure ()
"""
        with self.assertRaises(AssertionError) as ctx:
            parse_required_mir_wp_claims(tb_src)
        self.assertIn("NovelUnparsedClaim", str(ctx.exception))


if __name__ == "__main__":
    unittest.main()
