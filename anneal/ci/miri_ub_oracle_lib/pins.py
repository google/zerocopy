# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Loading and validation of the Miri oracle pin and the Tier B manifest."""

from __future__ import annotations

from collections import Counter
import hmac
import json
from pathlib import Path, PurePosixPath
import time
import urllib.parse
import urllib.request

from .common import (
    ALLOWED_API_HOSTS, ALLOWED_ARCHIVE_HOSTS, ALLOWED_ARCHIVE_URL_PREFIX, ALLOWED_PROFILES,
    ALLOWED_TIER_B_KINDS, DOWNLOAD_CHUNK_BYTES, HEX40_RE, HEX64_RE, MAX_CORPUS_DIR_DEPTH,
    MAX_PIN_BYTES, MAX_TIER_B_DIR_ENTRIES, OracleError, PIN_SCHEMA_VERSION, TIER_B_SCHEMA_VERSION,
    _read_regular_file_bytes, _validate_hex, _validate_positive_int,
)
from .corpus import _walk_corpus_tree


def load_pin(pin_path: Path) -> dict[str, object]:
    """Load and fail-closed validate `miri_oracle_pin.json`."""
    raw_bytes = _read_regular_file_bytes(
        pin_path, max_bytes=MAX_PIN_BYTES, label="--pin"
    )
    try:
        data = json.loads(raw_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise OracleError(f"failed to load pin '{pin_path}': {exc}") from exc

    if not isinstance(data, dict):
        raise OracleError("pin manifest must be a JSON object")
    if data.get("schema_version") != PIN_SCHEMA_VERSION:
        raise OracleError(
            f"unsupported pin schema_version: {data.get('schema_version')!r}"
        )
    if data.get("upstream_repo") != "rust-lang/miri":
        raise OracleError(
            "pin field 'upstream_repo' must equal 'rust-lang/miri', "
            f"got {data.get('upstream_repo')!r}"
        )

    miri_commit = _validate_hex(data.get("miri_commit"), HEX40_RE, "miri_commit")
    _validate_hex(data.get("rustc_commit"), HEX40_RE, "rustc_commit")
    _validate_hex(data.get("miri_tree_sha"), HEX40_RE, "miri_tree_sha")
    _validate_hex(data.get("fail_tree_sha"), HEX40_RE, "fail_tree_sha")
    if "fail_dep_tree_sha" in data:
        _validate_hex(
            data.get("fail_dep_tree_sha"), HEX40_RE, "fail_dep_tree_sha"
        )
    _validate_hex(data.get("archive_sha256"), HEX64_RE, "archive_sha256")
    _validate_hex(
        data.get("corpus_manifest_sha256"), HEX64_RE, "corpus_manifest_sha256"
    )

    archive_url = data.get("archive_url")
    expected_url = f"{ALLOWED_ARCHIVE_URL_PREFIX}{miri_commit}.tar.gz"
    if archive_url != expected_url:
        raise OracleError(
            f"archive_url must equal '{expected_url}', got {archive_url!r}"
        )

    expected_top_dir = data.get("expected_top_dir")
    if expected_top_dir != f"miri-{miri_commit}":
        raise OracleError(
            f"expected_top_dir must equal 'miri-{miri_commit}', "
            f"got {expected_top_dir!r}"
        )

    extract_subdirs = data.get("extract_subdirs")
    if not isinstance(extract_subdirs, list) or not extract_subdirs:
        raise OracleError("extract_subdirs must be a non-empty list of tests/*")
    seen_subdirs: set[str] = set()
    for raw_sub in extract_subdirs:
        if (
            not isinstance(raw_sub, str)
            or not raw_sub
            or "\\" in raw_sub
            or "\x00" in raw_sub
            or raw_sub.startswith("/")
        ):
            raise OracleError(f"invalid extract_subdirs entry: {raw_sub!r}")
        parts = raw_sub.split("/")
        if len(parts) < 2 or parts[0] != "tests":
            raise OracleError(
                f"extract_subdirs entry must be under 'tests/': {raw_sub!r}"
            )
        for seg in parts:
            if seg in ("", ".", "..") or ":" in seg:
                raise OracleError(
                    f"forbidden segment {seg!r} in extract_subdirs: {raw_sub!r}"
                )
        norm_sub = "/".join(parts)
        if norm_sub in seen_subdirs:
            raise OracleError(f"duplicate extract_subdirs entry: {raw_sub!r}")
        seen_subdirs.add(norm_sub)
    sorted_subdirs = sorted(seen_subdirs)
    for idx, prev in enumerate(sorted_subdirs):
        prefix = prev + "/"
        for nxt in sorted_subdirs[idx + 1 :]:
            if nxt.startswith(prefix):
                raise OracleError(
                    f"overlapping extract_subdirs entries: {prev!r} and {nxt!r}"
                )

    _validate_positive_int(data.get("expected_file_count"), "expected_file_count")
    if "expected_unit_count" in data:
        _validate_positive_int(data.get("expected_unit_count"), "expected_unit_count")
    if "max_harness_skips" in data:
        val = data.get("max_harness_skips")
        if isinstance(val, bool) or not isinstance(val, int) or val < 0:
            raise OracleError("pin field 'max_harness_skips' must be a non-negative int")
    if "max_rustc_or_harness_rejected" in data:
        val = data.get("max_rustc_or_harness_rejected")
        if isinstance(val, bool) or not isinstance(val, int) or val < 0:
            raise OracleError(
                "pin field 'max_rustc_or_harness_rejected' must be a non-negative int"
            )
    if "tests/fail-dep" in seen_subdirs and "fail_dep_tree_sha" not in data:
        raise OracleError(
            "pin must declare fail_dep_tree_sha when tests/fail-dep is extracted"
        )
    _validate_positive_int(data.get("fuel"), "fuel")
    min_caught = _validate_positive_int(data.get("min_caught_ub"), "min_caught_ub")
    if "expected_caught_ub_units" in data:
        exp_units = data.get("expected_caught_ub_units")
        if (
            not isinstance(exp_units, list)
            or not all(isinstance(u, str) and u for u in exp_units)
            or len(set(exp_units)) != len(exp_units)
        ):
            raise OracleError(
                "pin field 'expected_caught_ub_units' must be unique non-empty strings"
            )
        if len(exp_units) > min_caught:
            raise OracleError(
                "len(expected_caught_ub_units) cannot exceed min_caught_ub"
            )

    if data.get("max_unsound_accepts") != 0:
        raise OracleError("max_unsound_accepts must be 0 (fail-closed)")
    if data.get("max_tool_errors") != 0:
        raise OracleError("max_tool_errors must be 0 (fail-closed)")
    if data.get("capture_scope") != "crate":
        raise OracleError("capture_scope must be 'crate' (whole-crate oracle)")
    if data.get("profile") not in ALLOWED_PROFILES:
        raise OracleError(f"unsupported profile: {data.get('profile')!r}")
    if not isinstance(data.get("target"), str) or not data["target"]:
        raise OracleError("target must be a non-empty string")
    if "tier_b_corpus_sha256" in data:
        _validate_hex(
            data.get("tier_b_corpus_sha256"), HEX64_RE, "tier_b_corpus_sha256"
        )
    if "tier_b_min_counts" in data:
        min_counts = data.get("tier_b_min_counts")
        if not isinstance(min_counts, dict) or not min_counts:
            raise OracleError(
                "pin field 'tier_b_min_counts' must be a non-empty object"
            )
        for kind, floor in min_counts.items():
            if kind not in ALLOWED_TIER_B_KINDS:
                raise OracleError(
                    f"unsupported kind in tier_b_min_counts: {kind!r}"
                )
            _validate_positive_int(floor, f"tier_b_min_counts.{kind}")
    return data


def _validate_https_host(
    url: str, *, allowed_hosts: frozenset[str] = ALLOWED_ARCHIVE_HOSTS
) -> None:
    parsed = urllib.parse.urlparse(url)
    if parsed.scheme != "https":
        raise OracleError(f"refusing non-HTTPS archive URL: {url!r}")
    if parsed.hostname not in allowed_hosts:
        raise OracleError(
            f"refusing archive host {parsed.hostname!r} (allowed: "
            f"{sorted(allowed_hosts)})"
        )


class _PinnedHttpsRedirectHandler(urllib.request.HTTPRedirectHandler):
    """Fail closed on any redirect leaving HTTPS or allowed GitHub hosts."""

    def __init__(
        self, *, allowed_hosts: frozenset[str] = ALLOWED_ARCHIVE_HOSTS
    ) -> None:
        super().__init__()
        self._allowed_hosts = allowed_hosts

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        resolved = urllib.parse.urljoin(req.full_url, newurl)
        _validate_https_host(resolved, allowed_hosts=self._allowed_hosts)
        return super().redirect_request(req, fp, code, msg, headers, resolved)


def _fetch_pinned_github_json(
    url: str,
    *,
    deadline: float,
    max_bytes: int = MAX_PIN_BYTES,
) -> dict[str, object]:
    """Fetch bounded JSON from `api.github.com` under a wall-clock deadline."""
    _validate_https_host(url, allowed_hosts=ALLOWED_API_HOSTS)
    opener = urllib.request.build_opener(
        _PinnedHttpsRedirectHandler(allowed_hosts=ALLOWED_API_HOSTS)
    )
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": "anneal-miri-ub-oracle/1",
            "Accept": "application/vnd.github+json",
        },
    )
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise OracleError(f"upstream linkage check exceeded wall-clock deadline: {url}")
    buf = bytearray()
    try:
        with opener.open(req, timeout=remaining) as resp:
            _validate_https_host(resp.geturl(), allowed_hosts=ALLOWED_API_HOSTS)
            while True:
                rem = deadline - time.monotonic()
                if rem <= 0:
                    raise OracleError(
                        f"upstream linkage check exceeded wall-clock deadline: {url}"
                    )
                raw_sock = getattr(getattr(resp, "fp", None), "raw", None)
                sock = getattr(raw_sock, "_sock", None)
                if sock is not None and hasattr(sock, "settimeout"):
                    sock.settimeout(rem)
                chunk = resp.read(DOWNLOAD_CHUNK_BYTES)
                if time.monotonic() > deadline:
                    raise OracleError(
                        f"upstream linkage check exceeded wall-clock deadline: {url}"
                    )
                if not chunk:
                    break
                if len(buf) + len(chunk) > max_bytes:
                    raise OracleError(
                        f"upstream linkage JSON from '{url}' exceeds {max_bytes} B"
                    )
                buf.extend(chunk)
    except OracleError:
        raise
    except Exception as exc:
        raise OracleError(
            f"failed to query upstream linkage endpoint '{url}': {exc}"
        ) from exc
    try:
        parsed = json.loads(buf.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise OracleError(
            f"invalid JSON from upstream linkage endpoint '{url}': {exc}"
        ) from exc
    if not isinstance(parsed, dict):
        raise OracleError(
            f"expected JSON object from upstream linkage endpoint '{url}'"
        )
    return parsed


def _resolve_github_subtree_sha(
    repo: str,
    root_tree_sha: str,
    segments: tuple[str, ...],
    *,
    deadline: float,
) -> str:
    """Walk documented `/git/trees/{sha}` endpoints one segment at a time."""
    cur_sha = root_tree_sha
    walked: list[str] = []
    for seg in segments:
        tree_obj = _fetch_pinned_github_json(
            f"https://api.github.com/repos/{repo}/git/trees/{cur_sha}",
            deadline=deadline,
        )
        entries = tree_obj.get("tree")
        if not isinstance(entries, list):
            raise OracleError(f"{repo} tree {cur_sha} missing 'tree' list")
        match_sha: str | None = None
        for entry in entries:
            if (
                isinstance(entry, dict)
                and entry.get("path") == seg
                and entry.get("type") == "tree"
                and isinstance(entry.get("sha"), str)
                and HEX40_RE.fullmatch(entry["sha"])
            ):
                match_sha = entry["sha"]
                break
        walked.append(seg)
        if match_sha is None:
            raise OracleError(
                f"{repo} tree {root_tree_sha} missing subtree "
                f"'{'/'.join(walked)}'"
            )
        cur_sha = match_sha
    return cur_sha


def load_tier_b_manifest(
    tier_b_dir: Path,
    *,
    expected_corpus_sha256: str | None = None,
    min_kind_counts: dict[str, int] | None = None,
    max_entries: int = MAX_TIER_B_DIR_ENTRIES,
    max_depth: int = MAX_CORPUS_DIR_DEPTH,
    snapshot_dir: Path | None = None,
) -> dict[str, object]:
    """Load and validate Tier B manifest, fixture digests, and zero orphans.

    Uses the shared bounded streaming directory walker (`_walk_corpus_tree`) to
    hash `manifest.json` and every `.rs`/`.json` fixture in one pass, enforcing
    symlink/FIFO/depth/entry/size bounds without calling `os.walk`.
    """
    actual_corpus_sha, walked_files = _walk_corpus_tree(
        tier_b_dir,
        [""],
        suffixes=(".rs", ".json"),
        max_entries=max_entries,
        max_depth=max_depth,
        snapshot_dir=snapshot_dir,
        label="Tier B corpus",
    )
    if expected_corpus_sha256 is not None:
        if not hmac.compare_digest(actual_corpus_sha, expected_corpus_sha256):
            raise OracleError(
                f"Tier B corpus SHA-256 mismatch for '{tier_b_dir}': "
                f"expected {expected_corpus_sha256}, got {actual_corpus_sha}"
            )

    active_root = (
        snapshot_dir.resolve() if snapshot_dir is not None else tier_b_dir.resolve()
    )
    manifest_path = active_root / "manifest.json"
    raw_bytes = _read_regular_file_bytes(
        manifest_path, max_bytes=MAX_PIN_BYTES, label="Tier B manifest"
    )
    try:
        data = json.loads(raw_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise OracleError(
            f"failed to load Tier B manifest '{manifest_path}': {exc}"
        ) from exc

    if not isinstance(data, dict):
        raise OracleError("Tier B manifest must be a JSON object")
    if data.get("schema_version") != TIER_B_SCHEMA_VERSION:
        raise OracleError(
            f"unsupported Tier B schema_version: {data.get('schema_version')!r}"
        )
    fixtures = data.get("fixtures")
    if not isinstance(fixtures, list) or not fixtures:
        raise OracleError("Tier B manifest must contain a non-empty fixtures list")

    walked_set = set(walked_files)
    listed_paths: set[str] = set()
    ids: set[str] = set()
    kind_counts: Counter[str] = Counter()
    has_ub_caught = False
    has_valid_control = False

    for entry in fixtures:
        if not isinstance(entry, dict):
            raise OracleError("Tier B fixture entry must be an object")
        fid = entry.get("id")
        rel = entry.get("path")
        kind = entry.get("kind")
        category = entry.get("category")
        if not isinstance(fid, str) or not fid or fid in ids:
            raise OracleError(f"invalid or duplicate Tier B fixture id: {fid!r}")
        ids.add(fid)
        if (
            not isinstance(rel, str)
            or not rel
            or rel.startswith("/")
            or "\\" in rel
            or any(seg in ("", ".", "..") for seg in rel.split("/"))
        ):
            raise OracleError(f"invalid Tier B fixture path: {rel!r}")
        if rel in listed_paths:
            raise OracleError(f"duplicate Tier B fixture path: {rel!r}")
        listed_paths.add(rel)
        if kind not in ALLOWED_TIER_B_KINDS:
            raise OracleError(f"unsupported Tier B fixture kind: {kind!r}")
        kind_counts[kind] += 1
        if not isinstance(category, str) or not category:
            raise OracleError(f"Tier B fixture '{fid}' missing non-empty category")

        cur = active_root
        for part in PurePosixPath(rel).parts:
            cur = cur / part
            if cur.is_symlink():
                raise OracleError(
                    f"Tier B fixture path traverses or is a symlink: {rel!r}"
                )
        if rel not in walked_set or not cur.is_file():
            raise OracleError(f"Tier B fixture missing: {rel!r}")
        fpath = cur.resolve()
        try:
            fpath.relative_to(active_root)
        except ValueError as exc:
            raise OracleError(f"Tier B fixture escapes root: {rel!r}") from exc

        if kind in ("rust_ub_caught", "mir_ub_caught"):
            exp_sub = entry.get("expected_fault_substring")
            if not isinstance(exp_sub, str) or not exp_sub.strip():
                raise OracleError(
                    f"Tier B fixture '{fid}' ({kind}) requires non-empty "
                    f"expected_fault_substring"
                )
            has_ub_caught = True
        if kind in ("rust_valid_control", "mir_valid_control"):
            has_valid_control = True

        if "profile" in entry and entry["profile"] not in ALLOWED_PROFILES:
            raise OracleError(
                f"Tier B fixture '{fid}' has invalid profile: {entry['profile']!r}"
            )
        if "args" in entry:
            raw_args = entry["args"]
            if not isinstance(raw_args, list) or not all(
                isinstance(a, str) for a in raw_args
            ):
                raise OracleError(
                    f"Tier B fixture '{fid}' args must be a list of strings"
                )
        if "fuel" in entry:
            raw_fuel = entry["fuel"]
            if isinstance(raw_fuel, bool) or not isinstance(raw_fuel, int) or raw_fuel < 1:
                raise OracleError(
                    f"Tier B fixture '{fid}' fuel must be a positive integer"
                )
        if "edition" in entry and entry["edition"] not in ("2015", "2018", "2021", "2024"):
            raise OracleError(
                f"Tier B fixture '{fid}' has invalid edition: {entry['edition']!r}"
            )
        if "panic" in entry and entry["panic"] not in ("unwind", "abort"):
            raise OracleError(
                f"Tier B fixture '{fid}' has invalid panic: {entry['panic']!r}"
            )
        if "body" in entry:
            raw_body = entry["body"]
            if not isinstance(raw_body, str) or not raw_body:
                raise OracleError(
                    f"Tier B fixture '{fid}' body must be a non-empty string"
                )

    if not has_ub_caught:
        raise OracleError("Tier B manifest must include at least one *_ub_caught fixture")
    if not has_valid_control:
        raise OracleError(
            "Tier B manifest must include at least one *_valid_control fixture"
        )
    if min_kind_counts is not None:
        for req_kind, floor in sorted(min_kind_counts.items()):
            actual_cnt = kind_counts.get(req_kind, 0)
            if actual_cnt < floor:
                raise OracleError(
                    f"Tier B fixture count for {req_kind!r} regressed "
                    f"({actual_cnt} < pinned {floor})"
                )

    # Reject orphan `.rs` / `.json` fixtures discovered during the single
    # bounded walk so new files cannot be silently ignored by CI.
    disk_fixtures = walked_set - {"manifest.json"}
    orphans = sorted(disk_fixtures - listed_paths)
    if orphans:
        raise OracleError(
            f"Tier B corpus contains unlisted orphan fixtures: {', '.join(orphans)}"
        )

    return data
