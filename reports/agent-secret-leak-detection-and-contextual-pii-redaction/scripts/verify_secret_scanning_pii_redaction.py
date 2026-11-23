#!/usr/bin/env python3
"""Executable verification probe for secret-leak detection and contextual PII redaction.

Runs five self-contained, deterministic experiments using only the Python 3.10+
standard library and local `git` CLI subprocesses inside an ephemeral temporary
directory:

  1. Shannon-entropy alphabet ceiling, detect-secrets plugin/filter/transformer
     seams, gitleaks rule/allowlist behavior, and offline Base62 IEEE CRC-32
     checksum verification on 40-character classic GitHub tokens.
  2. Git object-graph secret persistence across working tree, reachable commit
     history (`git log --all`), unreachable amended/force-pushed objects
     (`git cat-file --batch-all-objects`), and `git gc --prune=now`.
  3. Text Anonymization Benchmark (TAB) conjunctive entity-level recall (`ER_di`)
     under coreference chains + a calibrated 300-entity synthetic fixture
     (`PERSON` + `CODE` + `QUASI`), plus exact reproduction of two live
     `evaluation.py` defects (`line 405` and `line 236`).
  4. Microsoft Presidio `PatternRecognizer` `MAX_SCORE=1.0` Luhn override,
     `UsSsnRecognizer` validation gaps, and `LemmaContextAwareEnhancer`
     substring/window/punctuation-tokenization (`ss#` vs. `ssn#`) blind spots.
  5. Constructive 5-scenario Contextual Integrity (CI) separation matrix across
     static NER span scrubbers, unisolated ReAct agents, one-shot `M_d(D, c_0)`,
     permissive conditional pre-release, and verified escalation gating.

All tokens and identifiers are generated synthetically in memory; zero real
credentials or personal data appear in source or output.
"""

from __future__ import annotations

from bisect import bisect_right
from collections import defaultdict
import configparser
from dataclasses import dataclass
import hashlib
import math
import os
import random
import re
import string
import subprocess
import tempfile
import zlib

BASE62_ALPHABET = string.digits + string.ascii_uppercase + string.ascii_lowercase

# TAB evaluation.py@558e09e26d6b constants (lines 14-16)
TAB_POS_TO_IGNORE = {"ADP", "PART", "CCONJ", "DET"}
TAB_TOKENS_TO_IGNORE = {"mr", "mrs", "ms", "no", "nr", "about"}
TAB_CHARACTERS_TO_IGNORE = " ,.-;:/&()[]\u2013'\" \u2019\u201c\u201d"


# ============================================================================
# Pillar 1: Pinned ports of Yelp/detect-secrets@5e141933 & gitleaks@5f6ec56c
# ============================================================================

DETECT_SECRETS_BASE64_CHARSET = (
    string.ascii_letters + string.digits + "+/" + "\\-_" + "="
)
DETECT_SECRETS_HEX_CHARSET = string.hexdigits

DETECT_SECRETS_KEYWORD_DENYLIST = (
    "api_?key",
    "auth_?key",
    "service_?key",
    "account_?key",
    "db_?key",
    "database_?key",
    "priv_?key",
    "private_?key",
    "client_?key",
    "db_?pass",
    "database_?pass",
    "key_?pass",
    "password",
    "passwd",
    "pwd",
    "secret",
    "contrase\u00f1a",
    "contrasena",
)


def ds_shannon_entropy(data: str, charset: str) -> float:
    """Port of HighEntropyStringsPlugin.calculate_shannon_entropy (lines 82-96)."""
    if not data:
        return 0.0
    entropy = 0.0
    for x in charset:
        p_x = float(data.count(x)) / len(data)
        if p_x > 0:
            entropy += -p_x * math.log(p_x, 2)
    return entropy


def ds_hex_shannon_entropy(data: str) -> float:
    """Port of HexHighEntropyString.calculate_shannon_entropy (lines 168-197)."""
    entropy = ds_shannon_entropy(data, DETECT_SECRETS_HEX_CHARSET)
    if len(data) == 1:
        return entropy
    try:
        int(data)
        entropy -= 1.2 / math.log(len(data), 2)
    except ValueError:
        pass
    return entropy


def ds_is_sequential_string(secret: str) -> bool:
    """Port of detect_secrets/filters/heuristic.py:is_sequential_string (lines 12-49)."""
    sequences = (
        string.ascii_uppercase + string.ascii_uppercase + string.digits + "+/",
        string.digits + string.ascii_uppercase + string.ascii_uppercase + "+/",
        (string.digits + string.ascii_uppercase) * 2,
        string.digits * 2,
        string.hexdigits.upper() + string.hexdigits.upper(),
        string.ascii_uppercase + "=/",
    )
    upper = secret.upper()
    return any(upper in seq for seq in sequences)


def ds_is_potential_uuid(secret: str) -> bool:
    """Port of detect_secrets/filters/heuristic.py:is_potential_uuid (lines 52-61)."""
    return bool(
        re.search(
            r"[a-f0-9]{8}\-[a-f0-9]{4}\-[a-f0-9]{4}\-[a-f0-9]{4}\-[a-f0-9]{12}",
            secret,
            re.IGNORECASE,
        )
    )


def ds_is_likely_id_string(secret: str, line: str, is_regex_detector: bool) -> bool:
    """Port of detect_secrets/filters/heuristic.py:is_likely_id_string (lines 64-84)."""
    try:
        idx = line.index(secret)
    except ValueError:
        return False
    if is_regex_detector:
        return False
    return bool(
        re.search(r"(^(id|myid|userid)|_id)s?[^a-z0-9]", line[:idx], re.IGNORECASE)
    )


def ds_is_not_alphanumeric_string(secret: str) -> bool:
    """Port of detect_secrets/filters/heuristic.py:is_not_alphanumeric_string (lines 220-225)."""
    return not bool(set(string.ascii_letters) & set(secret))


def ds_default_secret_filtered(secret: str, line: str, is_regex_detector: bool) -> bool:
    """Default secret-level heuristic filters in detect_secrets/settings.py:140-155."""
    return (
        ds_is_sequential_string(secret)
        or ds_is_potential_uuid(secret)
        or ds_is_likely_id_string(secret, line, is_regex_detector)
        or ds_is_not_alphanumeric_string(secret)
    )


_DS_B64_QUOTED_RE = re.compile(
    r'([\'"])([' + re.escape(DETECT_SECRETS_BASE64_CHARSET) + r"]+)(\1)"
)
_DS_HEX_QUOTED_RE = re.compile(
    r'([\'"])([' + re.escape(DETECT_SECRETS_HEX_CHARSET) + r"]+)(\1)"
)
_GH_CLASSIC_PREFIX = "gh" + "p_"
_GH_FINE_PREFIX = "github" + "_pat_"
_DS_GH_TOKEN_RE = re.compile(r"(ghp|gho|ghu|ghs|ghr)_[A-Za-z0-9_]{36}")
_DS_KW_QUOTES_REQ_EQ_RE = re.compile(
    r"("
    + "|".join(DETECT_SECRETS_KEYWORD_DENYLIST)
    + r")\w*(?:[]'\"]{0,2})?\s*(?:={1,3}|!==?)\s*(['\"`])"
    r"((?=[^\v'\"]*)(?=\w+)[^\v'\"]*[^\v,'\"`])(\2)",
    re.IGNORECASE,
)


def ds_scan_raw_lines_other_filetype(lines: list[str]) -> list[tuple[str, str]]:
    """Port of detect-secrets raw-line pass on FileType.OTHER (`.env` / `scan_diff`)."""
    findings: list[tuple[str, str]] = []
    for line in lines:
        line_s = line.rstrip()
        for m in _DS_GH_TOKEN_RE.finditer(line_s):
            tok = m.group(0)
            if not ds_default_secret_filtered(tok, line_s, is_regex_detector=True):
                findings.append(("GitHub Token", tok))
        for m in _DS_B64_QUOTED_RE.findall(line_s):
            cand = m[1]
            if ds_shannon_entropy(cand, DETECT_SECRETS_BASE64_CHARSET) > 4.5:
                if not ds_default_secret_filtered(cand, line_s, is_regex_detector=False):
                    findings.append(("Base64 High Entropy String", cand))
        for m in _DS_HEX_QUOTED_RE.findall(line_s):
            cand = m[1]
            if ds_hex_shannon_entropy(cand) > 3.0:
                if not ds_default_secret_filtered(cand, line_s, is_regex_detector=False):
                    findings.append(("Hex High Entropy String", cand))
        m_kw = _DS_KW_QUOTES_REQ_EQ_RE.search(line_s)
        if m_kw:
            cand = m_kw.group(3)
            if not ds_default_secret_filtered(cand, line_s, is_regex_detector=False):
                findings.append(("Secret Keyword", cand))
    return findings


def ds_eager_config_transform(raw_text: str) -> list[str] | None:
    """Port of EagerConfigFileTransformer (transformers/config.py:29-68, 90-103)."""
    parser = configparser.ConfigParser()
    parser.optionxform = str  # type: ignore[assignment]
    try:
        parser.read_string("[global]\n" + raw_text)
    except configparser.Error:
        return None
    out: list[str] = []
    for key, val in parser.items("global"):
        if not val:
            continue
        if len(val) >= 2 and val[0] in {"'", '"'} and val[-1] == val[0]:
            val = val[1:-1]
        val = val.replace('"', '\\"')
        out.append(f'{key} = "{val}"')
    return out


def ds_scan_env_file(raw_text: str) -> list[tuple[str, str]]:
    """Port of detect_secrets/core/scan.py:scan_file (lines 153-163, 253-281) on `.env`."""
    pass1 = ds_scan_raw_lines_other_filetype(raw_text.splitlines())
    if pass1:
        # scan.py:162-163 `if has_secret: break` aborts before eager transformers!
        return pass1
    transformed = ds_eager_config_transform(raw_text)
    if not transformed:
        return []
    return ds_scan_raw_lines_other_filetype(transformed)


def gitleaks_shannon_entropy(data: str) -> float:
    """Port of gitleaks@5f6ec56c detect/utils.go:shannonEntropy (lines 117-134).

    Note line 127 divides rune counts by UTF-8 byte length `len(data)`.
    """
    if data == "":
        return 0.0
    char_counts: dict[str, int] = {}
    for ch in data:
        char_counts[ch] = char_counts.get(ch, 0) + 1
    inv_length = 1.0 / float(len(data.encode("utf-8")))
    entropy = 0.0
    for count in char_counts.values():
        freq = float(count) * inv_length
        entropy -= freq * math.log2(freq)
    return entropy


_GL_GH_PAT_RE = re.compile(r"ghp_[0-9a-zA-Z]{36}")
_GL_GENERIC_RE = re.compile(
    r"""(?i)[\w.-]{0,50}?(?:access|auth|(?-i:[Aa]pi|API)|credential|creds|key|passw(?:or)?d|secret|token)(?:[ \t\w.-]{0,20})[\s'"]{0,3}(?:=|>|:{1,3}=|\|\||:|=>|\?=|,)[\x60'"\s=]{0,5}([\w.=-]{10,150}|[a-z0-9][a-z0-9+/]{11,}={0,3})(?:[\x60'"\s;]|\\[nr]|$)"""
)
_GL_GENERIC_ALPHA_ALLOW_RE = re.compile(r"^[a-zA-Z_.-]+$")


def gitleaks_detect_gh_pat(text: str) -> list[str]:
    """Port of gitleaks.toml:2158-2167 (`github-pat`, entropy = 3.0)."""
    hits: list[str] = []
    for m in _GL_GH_PAT_RE.finditer(text):
        sec = m.group(0)
        if gitleaks_shannon_entropy(sec) > 3.0:
            hits.append(sec)
    return hits


def gitleaks_detect_generic_api_key(line: str) -> list[str]:
    """Port of gitleaks.toml:637-657 (`generic-api-key`, entropy = 3.5 + alpha allowlist)."""
    hits: list[str] = []
    for m in _GL_GENERIC_RE.finditer(line):
        sec = m.group(1)
        if gitleaks_shannon_entropy(sec) <= 3.5:
            continue
        if _GL_GENERIC_ALPHA_ALLOW_RE.match(sec):
            continue
        hits.append(sec)
    return hits


def base62_encode_u32(val: int, width: int = 6) -> str:
    """Encode an unsigned 32-bit integer into fixed-width big-endian Base62."""
    chars: list[str] = []
    n = val & 0xFFFFFFFF
    while n > 0:
        n, rem = divmod(n, 62)
        chars.append(BASE62_ALPHABET[rem])
    while len(chars) < width:
        chars.append("0")
    return "".join(reversed(chars))


def make_synthetic_ghp_valid_crc(rng: random.Random) -> str:
    """Construct a synthetic 40-char classic PAT matching GitHub's CRC-32 layout."""
    body = "".join(rng.choice(BASE62_ALPHABET) for _ in range(30))
    crc = zlib.crc32(body.encode("ascii")) & 0xFFFFFFFF
    return _GH_CLASSIC_PREFIX + body + base62_encode_u32(crc, 6)


def verify_ghp_offline_crc32(token: str) -> bool:
    """Verify 40-char classic `ghp_<30 base62><6 base62 IEEE CRC-32>` offline.

    Each 30-char Base62 payload maps to exactly 1 canonical 6-char trailer in
    `["000000", "4gfFC3"]` (`62**-6` random Base62 acceptance; `2**-32` payload
    CRC-32 collision). Stateless `>40`-char `ghs_` tokens and `github_pat_` use
    distinct formats and must not be forced through `len == 40`.
    """
    if not token.startswith(_GH_CLASSIC_PREFIX) or len(token) != 40:
        return False
    payload = token[4:34]
    expected_sig = token[34:40]
    if any(ch not in BASE62_ALPHABET for ch in payload + expected_sig):
        return False
    crc = zlib.crc32(payload.encode("ascii")) & 0xFFFFFFFF
    return base62_encode_u32(crc, 6) == expected_sig


def run_probe_1() -> dict[str, object]:
    rng = random.Random(20261122)
    assert base62_encode_u32(0xFFFFFFFF, 6) == "4gfFC3"

    # (a) Mathematical alphabet ceiling vs. benign mixed-case identifier
    hex_key = hashlib.sha256(b"SYNTHETIC_TEST_HEX_KEY_SEED").hexdigest()
    benign_ident = "ThisIsAReallyLongString"
    h_hex_max = math.log2(16)
    h_hex_key = gitleaks_shannon_entropy(hex_key)
    h_benign = gitleaks_shannon_entropy(benign_ident)
    assert h_hex_key <= h_hex_max < h_benign, "Hex ceiling must be < benign camelCase H"

    # Multi-byte UTF-8 distortion in gitleaks shannonEntropy (detect/utils.go:127)
    utf8_sample = "\u00e9\u00fc\u00f1\u00f8\u00e5\u00df\u00e7\u00eb"  # 8 distinct 2-byte runes
    h_true_rune = math.log2(8)  # 3.0000 bits/rune
    h_gl_utf8 = gitleaks_shannon_entropy(utf8_sample)  # uses byte len 16 -> 2.0000!
    assert abs(h_true_rune - 3.0) < 1e-9 and abs(h_gl_utf8 - 2.0) < 1e-9

    # (b) detect-secrets HexHighEntropyString penalty vs. default filter pipeline
    digits_10 = "0123456789"
    digits_20_nonseq = "90817263541357924680"
    digits_19_plus_hex = "9081726354135792468a"
    h_d10 = ds_hex_shannon_entropy(digits_10)
    h_d20 = ds_hex_shannon_entropy(digits_20_nonseq)
    h_d19a = ds_hex_shannon_entropy(digits_19_plus_hex)
    assert h_d10 < 3.0 < h_d20 < h_d19a
    assert round(h_d19a, 4) == 3.4219
    d20_default_scan = ds_scan_raw_lines_other_filetype([f'trace_num = "{digits_20_nonseq}"'])
    d19a_default_scan = ds_scan_raw_lines_other_filetype([f'trace_num = "{digits_19_plus_hex}"'])
    assert len(d20_default_scan) == 0, "is_not_alphanumeric_string suppresses pure digits"
    assert len(d19a_default_scan) == 1, "Single hex letter bypasses both int() and alpha filter"

    # .env Pass-1 short-circuit shadowing (`scan.py:162-163`) & `scan_diff` gap (`scan.py:300`)
    unquoted_b64 = "SYNTHETIC_" + "k9Qm2Xp7Vz4Lw8Rn3Yt6Jc1Hb5Gd0FsA"
    pure_unquoted_env = f"CUSTOM_SERVICE_TOKEN={unquoted_b64}\n"
    shadowed_env = f'DB_PASSWORD="quoted_placeholder_pw"\nCUSTOM_SERVICE_TOKEN={unquoted_b64}\n'
    env_pure_hits = ds_scan_env_file(pure_unquoted_env)
    env_shadow_hits = ds_scan_env_file(shadowed_env)
    diff_hits = ds_scan_raw_lines_other_filetype([f"CUSTOM_SERVICE_TOKEN={unquoted_b64}"])
    assert any(v == unquoted_b64 for _, v in env_pure_hits), "EagerConfig catches pure unquoted .env"
    assert not any(v == unquoted_b64 for _, v in env_shadow_hits), "Pass-1 break shadows unquoted secret"
    assert len(diff_hits) == 0, "scan_diff runs zero file transformers"

    # gitleaks generic-api-key alpha allowlist & low-entropy password gap
    summer_pw = "Summer2025"
    diceware_pw = "correct-horse-battery-staple-alpha"
    h_summer = gitleaks_shannon_entropy(summer_pw)
    h_diceware = gitleaks_shannon_entropy(diceware_pw)
    assert round(h_summer, 4) == 2.9219 and h_summer <= 3.5
    assert round(h_diceware, 4) == 3.5581 and h_diceware > 3.5
    summer_hits = gitleaks_detect_generic_api_key(f'password = "{summer_pw}"')
    diceware_hits = gitleaks_detect_generic_api_key(f'password = "{diceware_pw}"')
    assert summer_hits == [] and diceware_hits == []

    # (c) Offline CRC-32 verification across 200 random un-checksummed fixtures & 50 valid-CRC tokens
    random_fixtures: list[str] = []
    while len(random_fixtures) < 200:
        cand = _GH_CLASSIC_PREFIX + "".join(rng.choice(BASE62_ALPHABET) for _ in range(36))
        if not verify_ghp_offline_crc32(cand):
            random_fixtures.append(cand)
    valid_crc_tokens = [make_synthetic_ghp_valid_crc(rng) for _ in range(50)]

    ds_fp = sum(
        1 for tok in random_fixtures if len(ds_scan_raw_lines_other_filetype([tok])) > 0
    )
    gl_fp = sum(1 for tok in random_fixtures if len(gitleaks_detect_gh_pat(tok)) > 0)
    crc_fp = sum(1 for tok in random_fixtures if verify_ghp_offline_crc32(tok))
    crc_tp = sum(1 for tok in valid_crc_tokens if verify_ghp_offline_crc32(tok))

    assert ds_fp == 200 and gl_fp == 200 and crc_fp == 0 and crc_tp == 50

    return {
        "h_hex_max": round(h_hex_max, 4),
        "h_hex_key": round(h_hex_key, 4),
        "h_benign": round(h_benign, 4),
        "h_gl_utf8_bug": round(h_gl_utf8, 4),
        "h_d10": round(h_d10, 4),
        "h_d20_plugin": round(h_d20, 4),
        "h_d19a": round(h_d19a, 4),
        "d20_default_alerts": len(d20_default_scan),
        "d19a_default_alerts": len(d19a_default_scan),
        "env_pure_caught": any(v == unquoted_b64 for _, v in env_pure_hits),
        "env_shadowed_caught": any(v == unquoted_b64 for _, v in env_shadow_hits),
        "env_diff_caught": len(diff_hits) > 0,
        "h_summer2025": round(h_summer, 4),
        "summer_alerts": len(summer_hits),
        "h_diceware": round(h_diceware, 4),
        "diceware_alerts": len(diceware_hits),
        "ds_fp": f"{ds_fp}/200",
        "gl_fp": f"{gl_fp}/200",
        "crc_fp": f"{crc_fp}/200",
        "crc_tp": f"{crc_tp}/50",
    }


# ============================================================================
# Pillar 2: Git Object-Graph Secret Persistence Matrix
# ============================================================================

def run_probe_2() -> dict[str, object]:
    rng = random.Random(20261123)
    tok_deleted = make_synthetic_ghp_valid_crc(rng)
    tok_amended = make_synthetic_ghp_valid_crc(rng)
    assert tok_deleted != tok_amended

    with tempfile.TemporaryDirectory() as tmpdir:
        repo = os.path.join(tmpdir, "repo")
        os.makedirs(repo)
        git_env = {
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "HOME": tmpdir,
            "XDG_CONFIG_HOME": tmpdir,
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_AUTHOR_NAME": "test",
            "GIT_AUTHOR_EMAIL": "test@example.invalid",
            "GIT_COMMITTER_NAME": "test",
            "GIT_COMMITTER_EMAIL": "test@example.invalid",
            "GIT_AUTHOR_DATE": "2025-01-01T00:00:00Z",
            "GIT_COMMITTER_DATE": "2025-01-01T00:00:00Z",
        }

        def git(*args: str, date_sec: int = 0, input_bytes: bytes | None = None) -> bytes:
            env = dict(git_env)
            ts = f"2025-01-01T00:00:{date_sec:02d}Z"
            env["GIT_AUTHOR_DATE"] = ts
            env["GIT_COMMITTER_DATE"] = ts
            cmd = [
                "git",
                "-C",
                repo,
                "-c",
                "commit.gpgsign=false",
                "-c",
                "init.defaultBranch=main",
                "-c",
                "user.name=test",
                "-c",
                "user.email=test@example.invalid",
                *args,
            ]
            return subprocess.check_output(cmd, env=env, input=input_bytes, stderr=subprocess.DEVNULL)

        git("init", "-q")

        # C1: Commit secret T1, then C2: `git rm` deletion commit (Meli et al. NDSS 2019 pattern)
        cfg_path = os.path.join(repo, "service.conf")
        with open(cfg_path, "w", encoding="utf-8") as f:
            f.write(f'auth_token = "{tok_deleted}"\n')
        git("add", "service.conf")
        git("commit", "-q", "-m", "Add service configuration", date_sec=1)
        c1_sha = git("rev-parse", "HEAD").decode().strip()

        git("rm", "-q", "service.conf")
        git("commit", "-q", "-m", "Remove config file", date_sec=2)

        # C3: Commit secret T2, then overwrite via `git commit --amend` -> C3'
        app_path = os.path.join(repo, "client.py")
        with open(app_path, "w", encoding="utf-8") as f:
            f.write(f'TOKEN = "{tok_amended}"\n')
        git("add", "client.py")
        git("commit", "-q", "-m", "Add client module", date_sec=3)
        dangling_c3_sha = git("rev-parse", "HEAD").decode().strip()

        with open(app_path, "w", encoding="utf-8") as f:
            f.write('TOKEN = os.environ["CLIENT_TOKEN"]\n')
        git("add", "client.py")
        git("commit", "-q", "--amend", "-m", "Add client module safely", date_sec=4)
        head_c3_prime_sha = git("rev-parse", "HEAD").decode().strip()

        # Tier 1: Working-tree scan (detect-secrets scan_file over tracked files)
        tracked = git("ls-files").decode().splitlines()
        wt_blob = ""
        for rel in tracked:
            with open(os.path.join(repo, rel), encoding="utf-8") as f:
                wt_blob += f.read()
        wt_vis = (tok_deleted in wt_blob, tok_amended in wt_blob)

        # Tier 2a: gitleaks git scan (`sources/git.go:93-94`)
        gl_patch = git(
            "log", "-p", "-U0", "--full-history", "--all", "--diff-filter=tuxdb"
        ).decode("utf-8", errors="replace")
        gl_vis = (tok_deleted in gl_patch, tok_amended in gl_patch)

        # Tier 2b: trufflehog two-phase gitparse (`pkg/gitparse/gitparse.go:401-406, 489-528`)
        revs = git("rev-list", "--full-history", "--all")
        th_patch = git(
            "log",
            "--patch",
            "--date=iso-strict",
            "--pretty=fuller",
            "--notes",
            "--diff-filter=AM",
            "--no-walk=unsorted",
            "--stdin",
            input_bytes=revs,
        ).decode("utf-8", errors="replace")
        th_vis = (tok_deleted in th_patch, tok_amended in th_patch)

        # Tier 3: Direct dangling commit lookup & full object-store scan
        dangling_commit_patch = git("show", dangling_c3_sha).decode("utf-8", errors="replace")
        all_objects_pre_gc = git("cat-file", "--batch-all-objects", "--batch").decode(
            "utf-8", errors="replace"
        )
        obj_pre_gc_vis = (
            tok_deleted in all_objects_pre_gc,
            tok_amended in all_objects_pre_gc,
        )
        assert tok_amended in dangling_commit_patch

        # Tier 4: Expire reflogs + prune unreachable objects (`git gc --prune=now`)
        git("reflog", "expire", "--expire=now", "--all")
        git("gc", "--prune=now", "--quiet")
        all_objects_post_gc = git("cat-file", "--batch-all-objects", "--batch").decode(
            "utf-8", errors="replace"
        )
        obj_post_gc_vis = (
            tok_deleted in all_objects_post_gc,
            tok_amended in all_objects_post_gc,
        )

        assert wt_vis == (False, False)
        assert gl_vis == (True, False)
        assert th_vis == (True, False)
        assert obj_pre_gc_vis == (True, True)
        assert obj_post_gc_vis == (True, False)

        return {
            "c1_sha": c1_sha[:12],
            "dangling_c3_sha": dangling_c3_sha[:12],
            "head_sha": head_c3_prime_sha[:12],
            "working_tree": wt_vis,
            "gitleaks_log_all": gl_vis,
            "trufflehog_revlist_all": th_vis,
            "object_store_pre_gc": obj_pre_gc_vis,
            "object_store_post_gc": obj_post_gc_vis,
        }


# ============================================================================
# Pillar 3: Port of TAB@558e09e2 evaluation.py & Live Bug Verification
# ============================================================================

@dataclass
class TabToken:
    idx: int
    text: str
    pos_: str

    @property
    def lower_(self) -> str:
        return self.text.lower()

    def __len__(self) -> int:
        return len(self.text)


@dataclass
class TabMaskedDocument:
    doc_id: str
    masked_spans: list[tuple[int, int]]
    _cached_offsets: set[int] | None = None

    def get_masked_offsets(self) -> set[int]:
        if self._cached_offsets is None:
            self._cached_offsets = {i for s, e in self.masked_spans for i in range(s, e)}
        return self._cached_offsets


@dataclass
class TabAnnotatedEntity:
    entity_id: str
    mentions: list[tuple[int, int]]
    need_masking: bool
    is_direct: bool
    entity_type: str
    mention_level_masking: list[bool]

    @property
    def mentions_to_mask(self) -> list[tuple[int, int]]:
        return [
            m for i, m in enumerate(self.mentions) if self.mention_level_masking[i]
        ]


def simple_tab_tokenize(text: str) -> list[TabToken]:
    """Deterministic tokenizer tagging honorifics/articles for TAB ignore rules."""
    det_adp = {"the", "a", "an", "of", "in", "on", "to", "for", "and", "or"}
    tokens: list[TabToken] = []
    for m in re.finditer(r"\w+|[^\w\s]", text):
        tok_text = m.group(0)
        pos = "DET" if tok_text.lower() in det_adp else "PROPN"
        tokens.append(TabToken(idx=m.start(), text=tok_text, pos_=pos))
    return tokens


class TabGoldDocument:
    """Faithful port of TAB@558e09e2 evaluation.py:GoldDocument (lines 338-515)."""

    def __init__(
        self,
        doc_id: str,
        text: str,
        entity_mentions: list[dict[str, object]],
        fix_bugs: bool = False,
    ) -> None:
        self.doc_id = doc_id
        self.text = text
        self._tokens: list[TabToken] | None = None
        self.fix_bugs = fix_bugs
        self.entities = {
            ent.entity_id: ent
            for ent in self._get_entities_from_mentions(entity_mentions)
        }

    @property
    def tokens(self) -> list[TabToken]:
        if self._tokens is None:
            self._tokens = simple_tab_tokenize(self.text)
        return self._tokens

    def _get_entities_from_mentions(
        self, entity_mentions: list[dict[str, object]]
    ) -> list[TabAnnotatedEntity]:
        entities: dict[str, TabAnnotatedEntity] = {}
        for mention in entity_mentions:
            entity_id = str(mention["entity_id"])
            start = int(mention["start_offset"])  # type: ignore[arg-type]
            end = int(mention["end_offset"])  # type: ignore[arg-type]
            id_type = str(mention["identifier_type"])
            need_masking = id_type in ("DIRECT", "QUASI")
            is_direct = id_type == "DIRECT"

            if entity_id in entities:
                cur = entities[entity_id]
                cur.mentions.append((start, end))
                cur.mention_level_masking.append(need_masking)
                if self.fix_bugs and is_direct:
                    cur.is_direct = True
            else:
                entities[entity_id] = TabAnnotatedEntity(
                    entity_id=entity_id,
                    mentions=[(start, end)],
                    need_masking=need_masking,
                    is_direct=is_direct,
                    entity_type=str(mention["entity_type"]),
                    mention_level_masking=[need_masking],
                )

        for ent in entities.values():
            if set(ent.mention_level_masking) != {ent.need_masking}:
                ent.need_masking = True
        return list(entities.values())

    def is_mention_masked(
        self, masked_doc: TabMaskedDocument, mention_start: int, mention_end: int
    ) -> bool:
        offsets_to_mask = set(range(mention_start, mention_end))
        non_covered = offsets_to_mask - masked_doc.get_masked_offsets()
        if non_covered:
            for tok in self.tokens:
                tok_end = tok.idx + len(tok)
                if tok_end > mention_start and tok.idx < mention_end:
                    if tok.pos_ in TAB_POS_TO_IGNORE or tok.lower_ in TAB_TOKENS_TO_IGNORE:
                        non_covered -= set(range(tok.idx, tok_end))
        for idx in list(non_covered):
            if self.text[idx] in set(TAB_CHARACTERS_TO_IGNORE):
                non_covered.remove(idx)
        return len(non_covered) == 0

    def is_masked(self, masked_doc: TabMaskedDocument, entity: TabAnnotatedEntity) -> bool:
        for incr, (m_start, m_end) in enumerate(entity.mentions):
            if self.is_mention_masked(masked_doc, m_start, m_end):
                continue
            if entity.mention_level_masking[incr]:
                return False
        return True

    def get_entities_to_mask(
        self, include_direct: bool = True, include_quasi: bool = True
    ) -> list[TabAnnotatedEntity]:
        out: list[TabAnnotatedEntity] = []
        for ent in self.entities.values():
            if not ent.need_masking:
                continue
            if ent.is_direct and not include_direct:
                continue
            if not ent.is_direct and not include_quasi:
                continue
            out.append(ent)
        return out

    def mention_recall(
        self,
        masked_doc: TabMaskedDocument,
        include_direct: bool = True,
        include_quasi: bool = True,
    ) -> float:
        """Port of `get_recall(..., token_level=False)` (`evaluation.py:169-199, 221-246`)."""
        masked_cnt = 0
        total_cnt = 0
        for ent in self.get_entities_to_mask(include_direct, include_quasi):
            # Bug in evaluation.py:236 uses `ent.mentions` instead of `ent.mentions_to_mask`!
            spans = ent.mentions_to_mask if self.fix_bugs else list(ent.mentions)
            for s, e in spans:
                if self.is_mention_masked(masked_doc, s, e):
                    masked_cnt += 1
                total_cnt += 1
        return masked_cnt / total_cnt if total_cnt else 0.0

    def entity_recall(
        self,
        masked_doc: TabMaskedDocument,
        include_direct: bool = True,
        include_quasi: bool = True,
    ) -> float:
        ents = self.get_entities_to_mask(include_direct, include_quasi)
        if not ents:
            return 0.0
        masked = sum(1 for e in ents if self.is_masked(masked_doc, e))
        return masked / len(ents)


def run_probe_3() -> dict[str, object]:
    rng = random.Random(20261124)

    # (a) Discourse title-drop coreference decay across chain lengths m in {1, 2, 4, 8, 12}
    # First mention ("Mr SyntheticApplicantAlpha") detected at r1 = 0.98; subsequent bare
    # surname mentions detected at r_anaphor = 0.60 across 2,000 synthetic entities per m.
    chain_curve: dict[int, tuple[float, float]] = {}
    for m_len in (1, 2, 4, 8, 12):
        n_trials = 2000
        mentions_masked_total = 0
        entities_masked_total = 0
        for t in range(n_trials):
            parts: list[str] = []
            mentions_meta: list[dict[str, object]] = []
            masked_spans: list[tuple[int, int]] = []
            cursor = 0
            for k in range(m_len):
                surface = "Mr SyntheticApplicantAlpha" if k == 0 else "SyntheticApplicantAlpha"
                seg = f"Clause {k}: {surface} testified. "
                s_off = cursor + seg.index(surface)
                e_off = s_off + len(surface)
                parts.append(seg)
                cursor += len(seg)
                mentions_meta.append(
                    {
                        "entity_id": f"e_{t}",
                        "start_offset": s_off,
                        "end_offset": e_off,
                        "identifier_type": "DIRECT",
                        "entity_type": "PERSON",
                    }
                )
                prob = 0.98 if k == 0 else 0.60
                if rng.random() < prob:
                    masked_spans.append((s_off, e_off))
                    mentions_masked_total += 1
            doc_text = "".join(parts)
            gdoc = TabGoldDocument("d", doc_text, mentions_meta)
            mdoc = TabMaskedDocument("d", masked_spans)
            if gdoc.is_masked(mdoc, gdoc.entities[f"e_{t}"]):
                entities_masked_total += 1
        mr = mentions_masked_total / (n_trials * m_len)
        er = entities_masked_total / n_trials
        chain_curve[m_len] = (round(mr, 3), round(er, 3))

    assert chain_curve[1][1] > 0.95
    assert chain_curve[4][0] > 0.68 and chain_curve[4][1] < 0.25
    assert chain_curve[8][0] > 0.63 and chain_curve[8][1] < 0.05

    # Calibrated 300-entity synthetic fixture (`50 PERSON + 50 CODE + 200 QUASI`,
    # evaluated at mention level `token_level=False`): illustrates how ~50% unrecognized
    # `CODE` direct identifiers + multi-mention `PERSON` decay drive `ER_di = 0.450`
    # while mention-level recall stays `0.720` (`ER_qi = 0.820`).
    mix_parts: list[str] = []
    mix_mentions: list[dict[str, object]] = []
    mix_masks: list[tuple[int, int]] = []
    pos = 0
    for idx in range(100):
        # 50 PERSON direct entities (half 1-mention, half 2-mention with 0.80 second-mention recall)
        # + 50 CODE direct entities (case numbers `400xx/01`, 0% default recognizer recall)
        if idx < 50:
            m_count = 1 if idx < 25 else 2
            for k in range(m_count):
                surf = f"ApplicantPerson{idx:02d}"
                chunk = f"Party {surf} appeared. "
                s = pos + chunk.index(surf)
                e = s + len(surf)
                mix_parts.append(chunk)
                pos += len(chunk)
                mix_mentions.append(
                    {
                        "entity_id": f"dir_{idx}",
                        "start_offset": s,
                        "end_offset": e,
                        "identifier_type": "DIRECT",
                        "entity_type": "PERSON",
                    }
                )
                if k == 0 or (idx % 5 != 0):
                    mix_masks.append((s, e))
        else:
            surf = f"{40000 + idx}/01"
            chunk = f"Application no. {surf} lodged. "
            s = pos + chunk.index(surf)
            e = s + len(surf)
            mix_parts.append(chunk)
            pos += len(chunk)
            mix_mentions.append(
                {
                    "entity_id": f"dir_{idx}",
                    "start_offset": s,
                    "end_offset": e,
                    "identifier_type": "DIRECT",
                    "entity_type": "CODE",
                }
            )
    # Add 200 single-mention QUASI dates masked at 82%
    for q in range(200):
        surf = f"14 January {1980 + (q % 40)}"
        chunk = f"On {surf} the hearing continued. "
        s = pos + chunk.index(surf)
        e = s + len(surf)
        mix_parts.append(chunk)
        pos += len(chunk)
        mix_mentions.append(
            {
                "entity_id": f"quasi_{q}",
                "start_offset": s,
                "end_offset": e,
                "identifier_type": "QUASI",
                "entity_type": "DATETIME",
            }
        )
        if q % 100 < 82:
            mix_masks.append((s, e))

    mix_doc = TabGoldDocument("mix", "".join(mix_parts), mix_mentions)
    mix_mdoc = TabMaskedDocument("mix", mix_masks)
    mix_mr_all = mix_doc.mention_recall(mix_mdoc, include_direct=True, include_quasi=True)
    mix_er_di = mix_doc.entity_recall(mix_mdoc, include_direct=True, include_quasi=False)
    mix_er_qi = mix_doc.entity_recall(mix_mdoc, include_direct=False, include_quasi=True)
    assert mix_mr_all > 0.70 and mix_er_di == 0.45 and mix_er_qi > 0.80

    # (b) Reproduce BOTH live bugs in TAB evaluation.py@558e09e2:
    # Bug 1 (`evaluation.py:405`): QUASI first mention -> DIRECT second mention (unmasked leak!)
    # Entity e1 is fully masked DIRECT; entity e2 has m0=QUASI (masked) and m1=DIRECT (UNMASKED!).
    bug_text = (
        "First party SyntheticDirectOne spoke. "
        "Then the claimant arrived; later SyntheticLeakedFullName testified. "
        "Council Europe Council concluded."
    )
    s_e1 = bug_text.index("SyntheticDirectOne")
    s_e2_m0 = bug_text.index("the claimant")
    s_e2_m1 = bug_text.index("SyntheticLeakedFullName")
    s_e3_m0 = bug_text.index("Council")
    s_e3_m1 = bug_text.rindex("Council")

    bug_mentions = [
        {
            "entity_id": "e1_direct",
            "start_offset": s_e1,
            "end_offset": s_e1 + len("SyntheticDirectOne"),
            "identifier_type": "DIRECT",
            "entity_type": "PERSON",
        },
        {
            "entity_id": "e2_quasi_then_direct",
            "start_offset": s_e2_m0,
            "end_offset": s_e2_m0 + len("the claimant"),
            "identifier_type": "QUASI",
            "entity_type": "PERSON",
        },
        {
            "entity_id": "e2_quasi_then_direct",
            "start_offset": s_e2_m1,
            "end_offset": s_e2_m1 + len("SyntheticLeakedFullName"),
            "identifier_type": "DIRECT",
            "entity_type": "PERSON",
        },
        # Bug 2 (`evaluation.py:236`): mixed QUASI + NO_MASK entity where QUASI is masked
        # and NO_MASK is rightly left unmasked!
        {
            "entity_id": "e3_mixed_nomask",
            "start_offset": s_e3_m0,
            "end_offset": s_e3_m0 + len("Council"),
            "identifier_type": "QUASI",
            "entity_type": "ORG",
        },
        {
            "entity_id": "e3_mixed_nomask",
            "start_offset": s_e3_m1,
            "end_offset": s_e3_m1 + len("Council"),
            "identifier_type": "NO_MASK",
            "entity_type": "ORG",
        },
    ]
    # Mask e1_direct, e2's m0 ("the claimant"), and e3's m0 (QUASI), leaving e2's DIRECT name unmasked!
    bug_masks = TabMaskedDocument(
        "bug",
        [
            (s_e1, s_e1 + len("SyntheticDirectOne")),
            (s_e2_m0, s_e2_m0 + len("the claimant")),
            (s_e3_m0, s_e3_m0 + len("Council")),
        ],
    )
    doc_buggy = TabGoldDocument("bug", bug_text, bug_mentions, fix_bugs=False)
    doc_fixed = TabGoldDocument("bug", bug_text, bug_mentions, fix_bugs=True)

    er_di_buggy = doc_buggy.entity_recall(bug_masks, include_direct=True, include_quasi=False)
    er_di_fixed = doc_fixed.entity_recall(bug_masks, include_direct=True, include_quasi=False)
    assert er_di_buggy == 1.0 and er_di_fixed == 0.5

    # Mask e2_m1 too so all required masks are covered, isolating Bug 2 (`evaluation.py:236`)
    all_req_masks = TabMaskedDocument(
        "bug",
        [
            *bug_masks.masked_spans,
            (s_e2_m1, s_e2_m1 + len("SyntheticLeakedFullName")),
        ],
    )
    mr_buggy = doc_buggy.mention_recall(all_req_masks, include_direct=True, include_quasi=True)
    mr_fixed = doc_fixed.mention_recall(all_req_masks, include_direct=True, include_quasi=True)
    assert round(mr_buggy, 3) == 0.800 and round(mr_fixed, 3) == 1.000

    return {
        "title_drop_curve": chain_curve,
        "mixed_corpus_mr": round(mix_mr_all, 3),
        "mixed_corpus_er_di": round(mix_er_di, 3),
        "mixed_corpus_er_qi": round(mix_er_qi, 3),
        "bug405_er_di_buggy_vs_fixed": (round(er_di_buggy, 3), round(er_di_fixed, 3)),
        "bug236_mr_buggy_vs_fixed": (round(mr_buggy, 3), round(mr_fixed, 3)),
    }


# ============================================================================
# Pillar 4: Port of Microsoft Presidio@61fde811 PatternRecognizer & Context
# ============================================================================

@dataclass
class PresidioSpan:
    entity_type: str
    start: int
    end: int
    score: float
    recognizer_name: str
    supportive_context: str = ""


class PresidioPatternRecognizerPort:
    """Faithful port of presidio_analyzer/pattern_recognizer.py:205-281."""

    MAX_SCORE = 1.0
    MIN_SCORE = 0.0

    def __init__(
        self,
        name: str,
        entity_type: str,
        patterns: list[tuple[str, re.Pattern[str], float]],
        context: list[str],
    ) -> None:
        self.name = name
        self.entity_type = entity_type
        self.patterns = patterns
        self.context = context

    def validate_result(self, pattern_text: str) -> bool | None:
        return None

    def invalidate_result(self, pattern_text: str) -> bool | None:
        return None

    def analyze(self, text: str) -> list[PresidioSpan]:
        results: list[PresidioSpan] = []
        for _pat_name, cregex, base_score in self.patterns:
            for m in cregex.finditer(text):
                s, e = m.span()
                cur = text[s:e]
                if not cur:
                    continue
                score = base_score
                val = self.validate_result(cur)
                if val is not None:
                    score = self.MAX_SCORE if val else self.MIN_SCORE
                inval = self.invalidate_result(cur)
                if inval is not None and inval:
                    score = self.MIN_SCORE
                if score > self.MIN_SCORE:
                    results.append(PresidioSpan(self.entity_type, s, e, score, self.name))
        # Deduplicate identical spans keeping max score (`EntityRecognizer.remove_duplicates`)
        best: dict[tuple[str, int, int], PresidioSpan] = {}
        for r in results:
            key = (r.entity_type, r.start, r.end)
            if key not in best or r.score > best[key].score:
                best[key] = r
        return sorted(best.values(), key=lambda x: (x.start, x.end))


class CreditCardRecognizerPort(PresidioPatternRecognizerPort):
    """Port of predefined_recognizers/generic/credit_card_recognizer.py:19-82."""

    def __init__(self) -> None:
        super().__init__(
            name="CreditCardRecognizer",
            entity_type="CREDIT_CARD",
            patterns=[
                (
                    "All Credit Cards (weak)",
                    re.compile(
                        r"\b(?!1\d{12}(?!\d))((4\d{3})|(5[0-5]\d{2})|(6\d{3})|(1\d{3})|(3\d{3}))"
                        r"[- ]?(\d{3,4})[- ]?(\d{3,4})[- ]?(\d{3,5})\b"
                    ),
                    0.3,
                )
            ],
            context=[
                "credit",
                "card",
                "visa",
                "mastercard",
                "cc ",
                "amex",
                "discover",
                "jcb",
                "diners",
                "maestro",
                "instapayment",
            ],
        )

    def validate_result(self, pattern_text: str) -> bool:
        sanitized = pattern_text.replace("-", "").replace(" ", "")
        digits = [int(d) for d in sanitized]
        checksum = sum(digits[-1::-2])
        for d in digits[-2::-2]:
            checksum += sum(int(x) for x in str(d * 2))
        return checksum % 10 == 0


class UsSsnRecognizerPort(PresidioPatternRecognizerPort):
    """Port of predefined_recognizers/country_specific/us/us_ssn_recognizer.py:18-88."""

    def __init__(self) -> None:
        super().__init__(
            name="UsSsnRecognizer",
            entity_type="US_SSN",
            patterns=[
                ("SSN1", re.compile(r"\b([0-9]{5})-([0-9]{4})\b"), 0.05),
                ("SSN2", re.compile(r"\b([0-9]{3})-([0-9]{6})\b"), 0.05),
                ("SSN3", re.compile(r"\b(([0-9]{3})-([0-9]{2})-([0-9]{4}))\b"), 0.05),
                ("SSN4", re.compile(r"\b[0-9]{9}\b"), 0.05),
                ("SSN5", re.compile(r"\b([0-9]{3})[- .]([0-9]{2})[- .]([0-9]{4})\b"), 0.5),
            ],
            context=["social", "security", "ssn", "ssns", "ssid"],
        )

    def invalidate_result(self, pattern_text: str) -> bool:
        delim_counts: dict[str, int] = defaultdict(int)
        for c in pattern_text:
            if c in (".", "-", " "):
                delim_counts[c] += 1
        if len(delim_counts) > 1:
            return True
        only_digits = "".join(c for c in pattern_text if c.isdigit())
        if all(only_digits[0] == c for c in only_digits):
            return True
        if only_digits[3:5] == "00" or only_digits[5:] == "0000":
            return True
        if only_digits[:3] in ("000", "666"):
            return True
        if only_digits in ("123456789", "987654320", "078051120"):
            return True
        return False


class UsLicenseDigitWeakPort(PresidioPatternRecognizerPort):
    """Port of UsLicenseRecognizer weak digits pattern (us_driver_license_recognizer.py:29-46)."""

    def __init__(self) -> None:
        super().__init__(
            name="UsLicenseRecognizer",
            entity_type="US_DRIVER_LICENSE",
            patterns=[("Driver License - Digits", re.compile(r"\b([0-9]{6,14}|[0-9]{16})\b"), 0.01)],
            context=["driver", "license", "permit", "lic", "identification", "dls", "cdls", "lic#", "driving"],
        )


def presidio_lemma_enhance(
    text: str,
    spans: list[PresidioSpan],
    recognizers: dict[str, PresidioPatternRecognizerPort],
    matching_mode: str = "substring",
    prefix_count: int = 5,
    suffix_count: int = 0,
) -> list[PresidioSpan]:
    """Faithful port of LemmaContextAwareEnhancer (lemma_context_aware_enhancer.py:35-384)."""
    # spaCy-like tokenization splitting punctuation (including `#`, `(`, `)`) into separate tokens
    raw_toks = [(m.group(0), m.start()) for m in re.finditer(r"[A-Za-z0-9]+|[^\w\s]", text)]
    tokens = [t for t, _ in raw_toks]
    indices = [idx for _, idx in raw_toks]
    stopwords = {"is", "the", "a", "an", "of", "for", "in", "to"}
    lemmas = [t.lower() for t in tokens]
    keywords = [lem for lem in lemmas if re.match(r"^[a-z0-9]+$", lem) and lem not in stopwords]

    out: list[PresidioSpan] = []
    for sp in spans:
        rec = recognizers[sp.recognizer_name]
        # Locate entity first token (context_aware_enhancer.py:161-169)
        first = bisect_right(indices, sp.start) - 1
        if first < 0 or indices[first] + len(tokens[first]) <= sp.start:
            first += 1

        def collect_dir(step: int, n_words: int) -> list[str]:
            i = first
            rem = n_words + 1
            collected: list[str] = []
            while 0 <= i < len(lemmas) and rem > 0:
                if lemmas[i] in keywords:
                    collected.append(lemmas[i])
                    rem -= 1
                i += step
            return collected

        ctx_words = sorted(set(collect_dir(-1, prefix_count) + collect_dir(1, suffix_count)))
        matched_word = ""
        for predef in rec.context:
            p_low = predef.lower()
            if matching_mode == "substring":
                ok = any(p_low in kw for kw in ctx_words)
            else:
                ok = any(p_low == kw for kw in ctx_words)
            if ok:
                matched_word = predef
                break
        new_score = sp.score
        if matched_word:
            new_score = min(max(new_score + 0.35, 0.4), 1.0)
        out.append(PresidioSpan(sp.entity_type, sp.start, sp.end, round(new_score, 2), sp.recognizer_name, matched_word))
    return out


def run_probe_4() -> dict[str, object]:
    rng = random.Random(20261125)
    cc_rec = CreditCardRecognizerPort()
    ssn_rec = UsSsnRecognizerPort()
    lic_rec = UsLicenseDigitWeakPort()
    recs = {r.name: r for r in (cc_rec, ssn_rec, lic_rec)}

    # (a) 10,000 synthetic 16-digit build/order IDs starting with '4' in zero-financial-context logs
    n_ids = 10_000
    luhn_max_score_fps = 0
    for _ in range(n_ids):
        oid = "4" + "".join(rng.choice(string.digits) for _ in range(15))
        line = f"ci_build_trace_id={oid} status=ok"
        hits = cc_rec.analyze(line)
        if any(h.score == 1.0 for h in hits):
            luhn_max_score_fps += 1
    assert 900 <= luhn_max_score_fps <= 1100, "Luhn collision rate must be ~10% (1/10)"

    # (b) UsSsnRecognizer: placeholder pruning (`123456789`), SSA 900-999 gap, and SSN4 ceiling
    assert ssn_rec.analyze("ssn 123456789") == [], "123456789 pruned by line 84 before context"
    itin_gap_hits = ssn_rec.analyze("record 900-12-3456")
    assert len(itin_gap_hits) == 1 and itin_gap_hits[0].score == 0.5

    ssn4_line = "employee ssn 234567891"
    ssn4_enhanced = presidio_lemma_enhance(ssn4_line, ssn_rec.analyze(ssn4_line), recs, "whole_word")
    assert len(ssn4_enhanced) == 1 and ssn4_enhanced[0].score == 0.40  # < 0.50 threshold!

    # (c) LemmaContextAwareEnhancer: substring false boost, `ss#` vs `ssn#` (`iss:1452`), & suffix=0
    dup_line = "duplicate job 84729104"
    sub_boost = presidio_lemma_enhance(dup_line, lic_rec.analyze(dup_line), recs, "substring")
    whole_boost = presidio_lemma_enhance(dup_line, lic_rec.analyze(dup_line), recs, "whole_word")
    assert sub_boost[0].score == 0.40 and sub_boost[0].supportive_context == "lic"
    assert whole_boost[0].score == 0.01 and whole_boost[0].supportive_context == ""

    # `ssn# 234567891` splits into `["ssn", "#", "234567891"]` and matches `"ssn"` in CONTEXT,
    # whereas `ss# 234567891` (`us_ssn_recognizer.py:33`, `iss:1452`) splits into `["ss", "#", ...]`
    # and fails even if `"ss#"` is appended to CONTEXT because `#` is stripped from `keywords`.
    ss_hash_line = "ss# 234567891"
    ssn_hash_line = "ssn# 234567891"
    ss_hash_res = presidio_lemma_enhance(ss_hash_line, ssn_rec.analyze(ss_hash_line), recs, "substring")
    ssn_hash_res = presidio_lemma_enhance(ssn_hash_line, ssn_rec.analyze(ssn_hash_line), recs, "whole_word")
    assert ss_hash_res[0].score == 0.05 and ssn_hash_res[0].score == 0.40

    ssn_with_ss_hash_ctx = UsSsnRecognizerPort()
    ssn_with_ss_hash_ctx.context = [*ssn_with_ss_hash_ctx.context, "ss#"]
    ss_hash_with_ctx_res = presidio_lemma_enhance(
        ss_hash_line,
        ssn_with_ss_hash_ctx.analyze(ss_hash_line),
        {"UsSsnRecognizer": ssn_with_ss_hash_ctx},
        "substring",
    )
    assert ss_hash_with_ctx_res[0].score == 0.05, "`ss#` in CONTEXT still fails punct-stripped keywords"

    suffix_line = "234567891 (ssn)"
    suffix_res = presidio_lemma_enhance(suffix_line, ssn_rec.analyze(suffix_line), recs, "whole_word")
    assert suffix_res[0].score == 0.05 and suffix_res[0].supportive_context == ""

    return {
        "luhn_contextless_fp": f"{luhn_max_score_fps}/{n_ids} ({luhn_max_score_fps / n_ids:.2%})",
        "placeholder_123456789_pruned": len(ssn_rec.analyze("ssn 123456789")) == 0,
        "invalid_ssa_900_12_3456_score": itin_gap_hits[0].score,
        "undelimited_ssn_with_context_score": ssn4_enhanced[0].score,
        "duplicate_lic_substring_vs_whole": (sub_boost[0].score, whole_boost[0].score),
        "ss_hash_vs_ssn_hash": (ss_hash_res[0].score, ssn_hash_res[0].score),
        "trailing_suffix_ssn_score": suffix_res[0].score,
    }


# ============================================================================
# Pillar 5: Constructive 5-Scenario Contextual-Integrity Separation Matrix
# ============================================================================

@dataclass(frozen=True)
class CiScenario:
    name: str
    task: str
    recipient: str
    unconditionally_required: frozenset[str]
    conditionally_required: dict[str, frozenset[str]]
    actual_trusted_condition: str | None
    tool_claimed_condition: str | None
    hijack_requested_fields: frozenset[str]
    implicit_norm_temptation_fields: frozenset[str]


def run_probe_5() -> dict[str, tuple[int, int, int]]:
    # Synthetic user vault mixing classic NER spans and non-NER relational/contextual secrets
    vault_is_ner_span = {
        "full_name": True,
        "callback_phone": True,
        "passport_number": True,
        "dietary_allergy": False,
        "rival_job_interview": False,
        "medical_leave_diagnosis": False,
    }
    all_fields = frozenset(vault_is_ner_span.keys())

    scenarios = [
        CiScenario(
            name="book_dinner_benign",
            task="restaurant_booking",
            recipient="bistro_api",
            unconditionally_required=frozenset({"full_name", "callback_phone", "dietary_allergy"}),
            conditionally_required={},
            actual_trusted_condition=None,
            tool_claimed_condition=None,
            hijack_requested_fields=frozenset(),
            implicit_norm_temptation_fields=frozenset(),
        ),
        CiScenario(
            name="book_dinner_hijacked",
            task="restaurant_booking",
            recipient="bistro_api",
            unconditionally_required=frozenset({"full_name", "callback_phone", "dietary_allergy"}),
            conditionally_required={},
            actual_trusted_condition=None,
            tool_claimed_condition=None,
            hijack_requested_fields=frozenset({"passport_number", "medical_leave_diagnosis"}),
            implicit_norm_temptation_fields=frozenset(),
        ),
        CiScenario(
            name="weekly_status_to_manager",
            task="status_update_email",
            recipient="current_manager",
            unconditionally_required=frozenset({"full_name"}),
            conditionally_required={},
            actual_trusted_condition=None,
            tool_claimed_condition=None,
            hijack_requested_fields=frozenset(),
            # Implicit-norm temptation: non-NER calendar/notes leak in action generation
            implicit_norm_temptation_fields=frozenset({"rival_job_interview", "medical_leave_diagnosis"}),
        ),
        CiScenario(
            name="flight_domestic_spoofed_intl",
            task="flight_booking",
            recipient="travel_portal_api",
            unconditionally_required=frozenset({"full_name", "callback_phone"}),
            conditionally_required={"intl_route": frozenset({"passport_number"})},
            actual_trusted_condition="domestic_route",
            tool_claimed_condition="intl_route",  # Malicious tool spoofs international branch!
            hijack_requested_fields=frozenset(),
            implicit_norm_temptation_fields=frozenset(),
        ),
        CiScenario(
            name="flight_genuine_intl",
            task="flight_booking",
            recipient="travel_portal_api",
            unconditionally_required=frozenset({"full_name", "callback_phone"}),
            conditionally_required={"intl_route": frozenset({"passport_number"})},
            actual_trusted_condition="intl_route",
            tool_claimed_condition="intl_route",
            hijack_requested_fields=frozenset(),
            implicit_norm_temptation_fields=frozenset(),
        ),
    ]

    def truly_authorized(sc: CiScenario) -> frozenset[str]:
        req = set(sc.unconditionally_required)
        if sc.actual_trusted_condition in sc.conditionally_required:
            req |= sc.conditionally_required[sc.actual_trusted_condition]
        return frozenset(req)

    def eval_architecture(policy: str) -> tuple[int, int, int]:
        utility_passes = 0
        leaked_scenarios = 0
        for sc in scenarios:
            auth = truly_authorized(sc)
            desired_by_agent = (
                set(sc.unconditionally_required)
                | sc.conditionally_required.get(sc.tool_claimed_condition or "", frozenset())
                | set(sc.hijack_requested_fields)
                | set(sc.implicit_norm_temptation_fields)
            )
            if policy == "static_ner_scrubber":
                # Strips all classic NER spans (`full_name`, `callback_phone`, `passport_number`),
                # passes all non-NER relational secrets untouched!
                available = {f for f in all_fields if not vault_is_ner_span[f]}
                sent = desired_by_agent & available
            elif policy == "unisolated_react_agent":
                sent = desired_by_agent
            elif policy == "airgap_strict_c0_only":
                # Evaluates M_d(D, c_0) strictly before tool interaction without conditional escalation
                available = set(sc.unconditionally_required)
                sent = desired_by_agent & available
            elif policy == "airgap_permissive_conditional":
                # Pre-releases union of potentially needed conditional fields for multi-hop tasks
                available = set(sc.unconditionally_required)
                for cond_fields in sc.conditionally_required.values():
                    available |= cond_fields
                sent = desired_by_agent & available
            elif policy == "airgap_verified_escalation_gate":
                # Releases unconditional c_0 fields + conditional fields ONLY on trusted attestation
                available = set(sc.unconditionally_required)
                if sc.actual_trusted_condition in sc.conditionally_required:
                    available |= sc.conditionally_required[sc.actual_trusted_condition]
                sent = desired_by_agent & available
            else:
                raise ValueError(policy)

            if auth <= sent:
                utility_passes += 1
            if len(sent - auth) > 0:
                leaked_scenarios += 1

        return utility_passes, leaked_scenarios, len(scenarios)

    results = {
        pol: eval_architecture(pol)
        for pol in (
            "static_ner_scrubber",
            "unisolated_react_agent",
            "airgap_strict_c0_only",
            "airgap_permissive_conditional",
            "airgap_verified_escalation_gate",
        )
    }

    # Constructive separation across the 5 threat/utility scenarios (`0/5` through `5/5`):
    assert results["static_ner_scrubber"] == (0, 2, 5)
    assert results["unisolated_react_agent"] == (5, 3, 5)
    assert results["airgap_strict_c0_only"] == (4, 0, 5)
    assert results["airgap_permissive_conditional"] == (5, 1, 5)
    assert results["airgap_verified_escalation_gate"] == (5, 0, 5)

    return results


def main() -> None:
    p1 = run_probe_1()
    p2 = run_probe_2()
    p3 = run_probe_3()
    p4 = run_probe_4()
    p5 = run_probe_5()

    print("=== PROBE 1 [deterministic port of detect-secrets@5e141933 & gitleaks@5f6ec56c + synthetic benchmark] ===")
    print(
        f"  alphabet_ceiling: H_hex_max={p1['h_hex_max']:.4f}, H_sha256_hex={p1['h_hex_key']:.4f} "
        f"< H('ThisIsAReallyLongString')={p1['h_benign']:.4f}; gitleaks_utf8_8rune_H={p1['h_gl_utf8_bug']:.4f} (true=3.0000)"
    )
    print(
        f"  detect_secrets_filters_and_env: H_d10={p1['h_d10']:.4f}, H_d20_plugin={p1['h_d20_plugin']:.4f}, "
        f"H_19d+1hex={p1['h_d19a']:.4f} (default_alerts={p1['d20_default_alerts']}, 19d+1hex_alerts={p1['d19a_default_alerts']}); "
        f"env_pure_caught={p1['env_pure_caught']}, env_shadowed_caught={p1['env_shadowed_caught']}, env_diff_caught={p1['env_diff_caught']}"
    )
    print(
        f"  gitleaks_generic_api_key: H('Summer2025')={p1['h_summer2025']:.4f} (alerts={p1['summer_alerts']}), "
        f"H('correct-horse-battery-staple-alpha')={p1['h_diceware']:.4f} (alpha_allowlist_alerts={p1['diceware_alerts']})"
    )
    print(
        f"  ghp_offline_crc32_gate: detect_secrets_fp={p1['ds_fp']}, gitleaks_fp={p1['gl_fp']} "
        f"-> offline_crc32_fp={p1['crc_fp']}, offline_crc32_recall={p1['crc_tp']}"
    )

    print("=== PROBE 2 [real git subprocess measurement + git-walk pipeline port] ===")
    print(
        f"  commits: c1={p2['c1_sha']}, dangling_c3={p2['dangling_c3_sha']}, head_c3_prime={p2['head_sha']}"
    )
    print(
        f"  visibility (T_deleted_commit, T_amended_dangling): working_tree={p2['working_tree']}, "
        f"gitleaks_log_all={p2['gitleaks_log_all']}, trufflehog_revlist_all={p2['trufflehog_revlist_all']}, "
        f"object_store_pre_gc={p2['object_store_pre_gc']}, object_store_post_gc={p2['object_store_post_gc']}"
    )

    print("=== PROBE 3 [deterministic port of TAB@558e09e2 evaluation.py + synthetic benchmark] ===")
    print(f"  discourse_title_drop_curve (m -> mention_recall, ER_di): {p3['title_drop_curve']}")
    print(
        f"  tab_synthetic_300ent_fixture (50 PERSON + 50 CODE + 200 QUASI, token_level=False): "
        f"mention_recall={p3['mixed_corpus_mr']:.3f}, ER_di={p3['mixed_corpus_er_di']:.3f}, ER_qi={p3['mixed_corpus_er_qi']:.3f}"
    )
    print(
        f"  live_evaluator_bugs: line405_ER_di_buggy_vs_fixed={p3['bug405_er_di_buggy_vs_fixed']}, "
        f"line236_MR_buggy_vs_fixed={p3['bug236_mr_buggy_vs_fixed']}"
    )

    print("=== PROBE 4 [deterministic port of microsoft/presidio@61fde811 + synthetic benchmark] ===")
    print(
        f"  credit_card_luhn_max_score_override: contextless_16digit_fp={p4['luhn_contextless_fp']}"
    )
    print(
        f"  us_ssn_and_context_enhancer: placeholder_123456789_pruned={p4['placeholder_123456789_pruned']}, "
        f"invalid_ssa_900_12_3456_score={p4['invalid_ssa_900_12_3456_score']:.2f}, "
        f"ssn4_with_context={p4['undelimited_ssn_with_context_score']:.2f}, "
        f"duplicate_lic_substring_vs_whole={p4['duplicate_lic_substring_vs_whole']}, "
        f"ss_hash_vs_ssn_hash={p4['ss_hash_vs_ssn_hash']}, "
        f"trailing_suffix_ssn={p4['trailing_suffix_ssn_score']:.2f}"
    )

    print("=== PROBE 5 [toy model: 5-scenario constructive contextual-integrity separation matrix] ===")
    for pol, (util_k, leak_k, total_n) in p5.items():
        print(
            f"  {pol}: task_utility={util_k}/{total_n} ({util_k / total_n:.3f}), "
            f"ci_leak_rate={leak_k}/{total_n} ({leak_k / total_n:.3f})"
        )
    print("ALL 5 SECRET-SCANNING & PII-REDACTION VERIFICATION PROBES PASSED.")


if __name__ == "__main__":
    main()
