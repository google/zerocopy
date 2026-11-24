# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Resolve, stamp, and verify commit-bound Anneal pre-release artifacts."""

from __future__ import annotations

import argparse
from collections.abc import Callable
from copy import deepcopy
from dataclasses import dataclass
import gzip
import hashlib
import http.client
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import time
import tomllib
from typing import BinaryIO
import urllib.error
import urllib.parse
import urllib.request
import zlib


REPO = Path(__file__).resolve().parents[2]
MANIFEST_REL = Path("anneal/trusted/cargo-anneal/Cargo.toml")
LOCK_REL = Path("anneal/Cargo.lock")
NON_STABLE_CHECK_REL = Path("anneal/ci/check_non_stable_version.sh")

ASSET_NAME = "anneal-toolchain-linux-x86_64.tar.zst"
DEV_VERSION = "0.0.0-dev"
UNPINNED = "0" * 64
LOCK_ENTRY_PREFIX = '[[package]]\nname = "cargo-anneal"\nversion = '

CRATES_API_URL = "https://crates.io/api/v1/crates/cargo-anneal"
STATIC_CRATES_PREFIX = "https://static.crates.io/crates/cargo-anneal"
USER_AGENT = (
    "zerocopy-anneal-release/1.0 (+https://github.com/google/zerocopy)"
)
HTTP_TIMEOUT_SECONDS = 15.0
HTTP_RETRY_BACKOFF_SECONDS = (2.0, 5.0)
TAG_POLL_INTERVAL_SECONDS = 5.0

HEX40_RE = re.compile(r"\A[0-9a-f]{40}\Z")
HEX64_RE = re.compile(r"\A[0-9a-f]{64}\Z")
ALPHA_VERSION_RE = re.compile(r"\A0\.2\.0-alpha\.([1-9][0-9]*)\Z")
SAFE_REL_SEG_RE = re.compile(r"\A[A-Za-z0-9._-]+\Z")

MAX_COMPRESSED_CRATE_BYTES = 16 * 1024 * 1024
MAX_UNCOMPRESSED_CRATE_BYTES = 64 * 1024 * 1024
MAX_CRATE_MEMBERS = 4096

ALLOWED_MANIFEST_TOP_KEYS = frozenset({
    "package",
    "lib",
    "bin",
    "example",
    "test",
    "bench",
    "features",
    "dependencies",
    "dev-dependencies",
    "build-dependencies",
    "target",
    "badges",
    "lints",
})


def _load_release_notes():
    spec = importlib.util.spec_from_file_location(
        "zerocopy_release_notes", REPO / ".github/release_notes.py"
    )
    if spec is None or spec.loader is None:
        raise RuntimeError("unable to load .github/release_notes.py")
    module = importlib.util.module_from_spec(spec)
    # Register before executing so `@dataclass` resolves `cls.__module__`.
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


release_notes = _load_release_notes()


@dataclass(frozen=True)
class ResolvedRelease:
    """Validated target commit and publication state for an Anneal release."""

    already_published: bool
    commit: str
    archive_sha256: str
    toolchain_tag: str
    published_crate_source_sha256: str

    def format_github_output(self) -> str:
        flag = "true" if self.already_published else "false"
        return (
            f"already_published={flag}\n"
            f"commit={self.commit}\n"
            f"archive_sha256={self.archive_sha256}\n"
            f"toolchain_tag={self.toolchain_tag}\n"
            f"published_crate_source_sha256="
            f"{self.published_crate_source_sha256}\n"
        )


@dataclass(frozen=True)
class CrateInspection:
    """Verified provenance and canonical source digest of a `.crate` archive."""

    commit: str
    archive_sha256: str
    toolchain_tag: str
    crate_source_sha256: str


def validate_commit_sha(value: str, *, label: str = "commit") -> str:
    if not isinstance(value, str) or not HEX40_RE.fullmatch(value):
        raise ValueError(f"invalid 40-hex {label}: {value!r}")
    return value


def validate_nonzero_sha256(value: str, *, label: str = "sha256") -> str:
    if (
        not isinstance(value, str)
        or not HEX64_RE.fullmatch(value)
        or value == UNPINNED
    ):
        raise ValueError(f"invalid nonzero 64-hex {label}: {value!r}")
    return value


def parse_anneal_prerelease_version(version: str):
    """Parse `version` as an allowed `0.2.0-alpha.<N>` pre-release."""
    if (
        not isinstance(version, str)
        or not version
        or version != version.strip()
        or "/" in version
    ):
        raise ValueError(f"invalid Anneal version: {version!r}")
    tag = release_notes.validate_tag_name(
        f"anneal-v{version}", flag_name="version"
    )
    prefix, semver = release_notes.parse_tag(tag)
    if prefix != "anneal-v" or tag != f"anneal-v{version}":
        raise ValueError(f"invalid Anneal version: {version!r}")
    # FIXME(#4012): Keep stable SemVer blocked until all #4012 items close.
    if not semver.is_prerelease:
        raise ValueError(
            f"stable Anneal version {version!r} is blocked until #4012 closes"
        )
    if ALPHA_VERSION_RE.fullmatch(version) is None:
        raise ValueError(
            f"expected a 0.2.0-alpha.<N> Anneal version, got {version!r}"
        )
    return semver


def toolchain_tag_and_url(commit: str, sha256: str) -> tuple[str, str]:
    """Return `(tag, url)` for commit `commit` and archive digest `sha256`."""
    validate_commit_sha(commit, label="commit")
    validate_nonzero_sha256(sha256, label="sha256")
    tag = f"anneal-toolchain-{commit[:12]}-{sha256[:16]}"
    url = (
        f"https://github.com/google/zerocopy/releases/download/{tag}/"
        f"{ASSET_NAME}"
    )
    return tag, url


def _canonical_json_sha256(obj: object) -> str:
    encoded = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode(
        "utf-8"
    )
    return hashlib.sha256(encoded).hexdigest()


def _normalize_dep_table(table: object) -> dict[str, object]:
    if table is None:
        return {}
    if not isinstance(table, dict):
        raise ValueError("dependency table must be a TOML table")
    return {
        name: ({"version": spec} if isinstance(spec, str) else spec)
        for name, spec in table.items()
    }


def _canonicalize_manifest(
    ast: dict[str, object],
    *,
    label: str,
    version: str,
    files: dict[str, tuple[int, bytes]],
    is_generated: bool,
) -> dict[str, object]:
    """Project `Cargo.toml.orig` or Cargo-generated `Cargo.toml` to one normal
    form so any unapproved field or target drift fails closed."""
    unexpected_top = set(ast) - ALLOWED_MANIFEST_TOP_KEYS
    if unexpected_top:
        raise ValueError(
            f"{label} has unexpected top-level keys: {sorted(unexpected_top)}"
        )

    raw_pkg = ast.get("package")
    if not isinstance(raw_pkg, dict):
        raise ValueError(f"{label} missing [package] table")
    pkg = dict(raw_pkg)
    if pkg.get("name") != "cargo-anneal" or pkg.get("version") != version:
        raise ValueError(f"{label} package name or version mismatch")
    if pkg.get("links") is not None:
        raise ValueError(f"{label} must not configure package.links")
    if is_generated:
        if pkg.get("build") not in (None, False, "build.rs"):
            raise ValueError(
                f"{label} unexpected synthesized package.build: "
                f"{pkg.get('build')!r}"
            )
        pkg.pop("build", None)
    elif pkg.get("build") is not None:
        raise ValueError(f"{label} must not set package.build explicitly")

    if is_generated:
        for auto_key in (
            "autolib",
            "autobins",
            "autoexamples",
            "autotests",
            "autobenches",
        ):
            if auto_key in pkg:
                if not isinstance(pkg[auto_key], bool):
                    raise ValueError(f"{label} invalid boolean {auto_key}")
                pkg.pop(auto_key)
        if "resolver" in pkg:
            if pkg["resolver"] not in ("2", "3"):
                raise ValueError(
                    f"{label} unexpected synthesized resolver: "
                    f"{pkg['resolver']!r}"
                )
            pkg.pop("resolver")
    else:
        pkg.pop("resolver", None)

    if "README.md" in files:
        readme_val = pkg.get("readme")
        if readme_val is None or (
            isinstance(readme_val, str)
            and (readme_val == "README.md" or readme_val.endswith("/README.md"))
        ):
            pkg["readme"] = "README.md"

    exo = pkg.get("metadata", {}).get("exocrate") if isinstance(
        pkg.get("metadata"), dict
    ) else None
    if (
        not isinstance(exo, list)
        or len(exo) != 1
        or not isinstance(exo[0], dict)
    ):
        raise ValueError(f"{label} invalid [[package.metadata.exocrate]]")

    if "lib" in ast:
        raw_lib = ast["lib"]
        if not isinstance(raw_lib, dict):
            raise ValueError(f"{label} invalid [lib] table")
        if raw_lib.get("proc-macro") or raw_lib.get("proc_macro"):
            raise ValueError(f"{label} must not declare a proc-macro target")
        lib_norm: dict[str, object] | None = {
            **raw_lib,
            "name": raw_lib.get("name", "cargo_anneal"),
            "path": raw_lib.get("path", "src/lib.rs"),
        }
    elif "src/lib.rs" in files:
        lib_norm = {"name": "cargo_anneal", "path": "src/lib.rs"}
    else:
        lib_norm = None

    raw_bins = ast.get("bin")
    if (
        not isinstance(raw_bins, list)
        or len(raw_bins) != 1
        or not isinstance(raw_bins[0], dict)
        or raw_bins[0].get("name") != "cargo-anneal"
    ):
        raise ValueError(f"{label} must declare only the cargo-anneal bin")
    bin_entry = {
        **raw_bins[0],
        "path": raw_bins[0].get("path", "src/main.rs"),
    }
    if bin_entry["path"] not in files:
        raise ValueError(
            f"{label} bin path {bin_entry['path']!r} missing from .crate"
        )

    examples_norm: list[dict[str, object]] = []
    if "example" in ast:
        raw_examples = ast["example"]
        if not isinstance(raw_examples, list):
            raise ValueError(f"{label} invalid [[example]] list")
        for item in raw_examples:
            if not isinstance(item, dict) or not isinstance(
                item.get("name"), str
            ):
                raise ValueError(f"{label} invalid [[example]] entry")
            ex_path = item.get("path", f"examples/{item['name']}.rs")
            if ex_path not in files:
                raise ValueError(
                    f"{label} example path {ex_path!r} missing from .crate"
                )
            examples_norm.append({**item, "path": ex_path})

    allowed_dep_sections = {
        "dependencies",
        "dev-dependencies",
        "build-dependencies",
    }
    raw_targets = ast.get("target", {})
    if not isinstance(raw_targets, dict):
        raise ValueError(f"{label} invalid [target] table")
    targets_norm: dict[str, dict[str, object]] = {}
    for cfg_key, cfg_tbl in raw_targets.items():
        if not isinstance(cfg_tbl, dict):
            raise ValueError(f"{label} invalid target.{cfg_key} table")
        bad_cfg_keys = set(cfg_tbl) - allowed_dep_sections
        if bad_cfg_keys:
            raise ValueError(
                f"{label} target.{cfg_key} has unexpected keys: "
                f"{sorted(bad_cfg_keys)}"
            )
        targets_norm[cfg_key] = {
            dep_k: _normalize_dep_table(cfg_tbl.get(dep_k))
            for dep_k in sorted(allowed_dep_sections)
        }

    return {
        "package": pkg,
        "lib": lib_norm,
        "bin": [bin_entry],
        "example": examples_norm,
        "test": ast.get("test", []),
        "bench": ast.get("bench", []),
        "features": ast.get("features", {}),
        "dependencies": _normalize_dep_table(ast.get("dependencies")),
        "dev-dependencies": _normalize_dep_table(ast.get("dev-dependencies")),
        "build-dependencies": _normalize_dep_table(
            ast.get("build-dependencies")
        ),
        "target": targets_norm,
        "badges": ast.get("badges", {}),
        "lints": ast.get("lints", {}),
    }


def _read_bounded_stream(
    stream: BinaryIO,
    limit: int,
    error_message: str,
    *,
    chunk_size: int = 256 * 1024,
) -> bytes:
    """Read `stream` in bounded chunks, failing closed above `limit` bytes."""
    chunks: list[bytes] = []
    total = 0
    while True:
        chunk = stream.read(min(chunk_size, limit - total + 1))
        if not chunk:
            return b"".join(chunks)
        total += len(chunk)
        if total > limit:
            raise ValueError(error_message)
        chunks.append(chunk)


def inspect_crate_archive(
    raw_bytes: bytes,
    *,
    version: str,
    expected_commit: str | None = None,
    expected_sha256: str | None = None,
) -> CrateInspection:
    """Validate a `cargo-anneal-<version>.crate` archive purely in memory."""
    parse_anneal_prerelease_version(version)
    if expected_commit is not None:
        validate_commit_sha(expected_commit, label="expected_commit")
    if expected_sha256 is not None:
        validate_nonzero_sha256(expected_sha256, label="expected_sha256")
    if len(raw_bytes) > MAX_COMPRESSED_CRATE_BYTES:
        raise ValueError("compressed .crate exceeds 16 MiB limit")

    prefix = f"cargo-anneal-{version}/"
    seen: set[str] = set()
    files: dict[str, tuple[int, bytes]] = {}
    member_count = 0
    total_payload_bytes = 0

    try:
        # Decompress up front with a hard 64 MiB cap and open the inner archive
        # in plain uncompressed tar mode (`r:`) so neither PAX/GNU headers nor
        # nested `.tar.{xz,bz2,gz}` streams can bypass the 64 MiB bound.
        with gzip.GzipFile(fileobj=io.BytesIO(raw_bytes), mode="rb") as gz:
            tar_bytes = _read_bounded_stream(
                gz,
                MAX_UNCOMPRESSED_CRATE_BYTES,
                "uncompressed .crate exceeds 64 MiB limit",
            )

        with tarfile.open(fileobj=io.BytesIO(tar_bytes), mode="r:") as archive:
            for member in archive:
                member_count += 1
                if member_count > MAX_CRATE_MEMBERS:
                    raise ValueError(".crate exceeds maximum member count")
                if not member.isreg() or member.issparse() or member.size < 0:
                    raise ValueError(
                        f"non-regular tar entry in .crate: {member.name!r}"
                    )
                name = member.name
                if (
                    "\\" in name
                    or name.startswith("/")
                    or not name.startswith(prefix)
                ):
                    raise ValueError(
                        f".crate entry outside {prefix!r}: {name!r}"
                    )
                rel = name[len(prefix) :]
                segments = rel.split("/")
                if not rel or any(
                    seg in ("", ".", "..") or not SAFE_REL_SEG_RE.fullmatch(seg)
                    for seg in segments
                ):
                    raise ValueError(
                        f"unnormalized or unsafe .crate member path: {rel!r}"
                    )
                if rel != ".cargo_vcs_info.json" and any(
                    seg.startswith(".") for seg in segments
                ):
                    raise ValueError(
                        f"forbidden hidden or config path in .crate: {rel!r}"
                    )
                if rel == "rust-toolchain" or rel.startswith("rust-toolchain."):
                    raise ValueError(
                        f"forbidden rust-toolchain file in .crate: {rel!r}"
                    )
                if rel.startswith("src/bin/"):
                    raise ValueError(
                        f"forbidden implicit bin in .crate: {rel!r}"
                    )
                if rel in seen:
                    raise ValueError(
                        f"duplicate .crate member path: {rel!r}"
                    )
                seen.add(rel)
                remaining = MAX_UNCOMPRESSED_CRATE_BYTES - total_payload_bytes
                if member.size > remaining:
                    raise ValueError("uncompressed .crate exceeds 64 MiB limit")
                handle = archive.extractfile(member)
                if handle is None:
                    raise ValueError(f"unreadable .crate member: {rel!r}")
                # Read in bounded chunks up to `remaining` rather than
                # `handle.read(member.size + 1)` so crafted headers cannot
                # trigger large buffer pre-allocations.
                data = _read_bounded_stream(
                    handle,
                    remaining,
                    "uncompressed .crate exceeds 64 MiB limit",
                )
                if len(data) != member.size:
                    raise ValueError(
                        f"size mismatch reading .crate member: {rel!r}"
                    )
                total_payload_bytes += len(data)
                if total_payload_bytes > MAX_UNCOMPRESSED_CRATE_BYTES:
                    raise ValueError("uncompressed .crate exceeds 64 MiB limit")
                exec_bit = 1 if (member.mode & 0o111) else 0
                files[rel] = (exec_bit, data)
    except (OSError, EOFError, zlib.error, tarfile.TarError) as err:
        raise ValueError(f"corrupt .crate archive: {err}") from err

    required_members = (
        "Cargo.toml",
        "Cargo.toml.orig",
        "Cargo.lock",
        ".cargo_vcs_info.json",
        "build.rs",
        "packaged/bundled_resources.rs",
    )
    for req in required_members:
        if req not in files:
            raise ValueError(f"missing required .crate member: {req}")
        if files[req][0] != 0:
            raise ValueError(f"unexpected executable mode on {req}")

    try:
        vcs = json.loads(files[".cargo_vcs_info.json"][1].decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as err:
        raise ValueError(f"invalid .cargo_vcs_info.json: {err}") from err
    if (
        not isinstance(vcs, dict)
        or vcs.get("path_in_vcs") != "anneal/trusted/cargo-anneal"
    ):
        raise ValueError("unexpected .cargo_vcs_info.json path_in_vcs")
    git_obj = vcs.get("git")
    if not isinstance(git_obj, dict):
        raise ValueError("missing .cargo_vcs_info.json git object")
    commit = git_obj.get("sha1")
    if not isinstance(commit, str) or not HEX40_RE.fullmatch(commit):
        raise ValueError(f"invalid .cargo_vcs_info.json git.sha1: {commit!r}")
    if "dirty" in git_obj and not isinstance(git_obj["dirty"], bool):
        raise ValueError("invalid .cargo_vcs_info.json git.dirty field")
    if expected_commit is not None and commit != expected_commit:
        raise ValueError(
            f".crate commit {commit} does not match expected {expected_commit}"
        )

    try:
        orig_ast = tomllib.loads(files["Cargo.toml.orig"][1].decode("utf-8"))
        gen_ast = tomllib.loads(files["Cargo.toml"][1].decode("utf-8"))
        lock_ast = tomllib.loads(files["Cargo.lock"][1].decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as err:
        raise ValueError(f"invalid TOML in .crate: {err}") from err

    canonical_orig = _canonicalize_manifest(
        orig_ast,
        label="Cargo.toml.orig",
        version=version,
        files=files,
        is_generated=False,
    )
    canonical_gen = _canonicalize_manifest(
        gen_ast,
        label="Cargo.toml",
        version=version,
        files=files,
        is_generated=True,
    )
    if canonical_orig != canonical_gen:
        raise ValueError("Cargo.toml diverged from Cargo.toml.orig")

    exo_entry = orig_ast["package"]["metadata"]["exocrate"][0]
    sha256 = exo_entry.get("sha256", "")
    tag, expected_url = toolchain_tag_and_url(commit, sha256)
    if exo_entry != {
        "os": "linux",
        "arch": "x86_64",
        "sha256": sha256,
        "url": expected_url,
    }:
        raise ValueError(f"unexpected exocrate entry: {exo_entry!r}")
    if expected_sha256 is not None and sha256 != expected_sha256:
        raise ValueError(
            f".crate archive sha256 {sha256} != expected {expected_sha256}"
        )

    lock_pkgs = [
        pkg
        for pkg in lock_ast.get("package", [])
        if isinstance(pkg, dict) and pkg.get("name") == "cargo-anneal"
    ]
    if len(lock_pkgs) != 1 or lock_pkgs[0].get("version") != version:
        raise ValueError("packaged Cargo.lock cargo-anneal version mismatch")

    # Hash structured JSON tuples over `Cargo.toml.orig` and `Cargo.lock` ASTs
    # alongside raw packaged file digests so `crate_source_sha256` is free of
    # delimiter collisions while remaining invariant across minor `cargo`
    # upgrades on GitHub-hosted runners.
    records: list[list[object]] = []
    for rel in sorted(files):
        exec_bit, data = files[rel]
        if rel == "Cargo.toml":
            records.append(["Cargo.toml", "validated"])
        elif rel == ".cargo_vcs_info.json":
            records.append(
                [".cargo_vcs_info.json", commit, "anneal/trusted/cargo-anneal"]
            )
        elif rel == "Cargo.toml.orig":
            records.append(
                ["Cargo.toml.orig", 0, _canonical_json_sha256(orig_ast)]
            )
        elif rel == "Cargo.lock":
            records.append(["Cargo.lock", 0, _canonical_json_sha256(lock_ast)])
        else:
            digest = hashlib.sha256(data).hexdigest()
            records.append([rel, exec_bit, digest])

    source_sha256 = _canonical_json_sha256(records)
    return CrateInspection(
        commit=commit,
        archive_sha256=sha256,
        toolchain_tag=tag,
        crate_source_sha256=source_sha256,
    )


class _HttpsOnlyRedirectHandler(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        parsed = urllib.parse.urlsplit(newurl)
        if parsed.scheme != "https" or not parsed.netloc:
            raise urllib.error.URLError(
                f"refusing non-HTTPS redirect to {newurl!r}"
            )
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def _http_get_bytes(
    url: str,
    *,
    max_bytes: int = MAX_COMPRESSED_CRATE_BYTES,
    sleep_fn: Callable[[float], None] = time.sleep,
) -> tuple[int, bytes]:
    parsed = urllib.parse.urlsplit(url)
    if parsed.scheme != "https" or parsed.netloc not in (
        "crates.io",
        "static.crates.io",
    ):
        raise ValueError(f"unexpected HTTP URL host: {url!r}")
    opener = urllib.request.build_opener(_HttpsOnlyRedirectHandler())
    headers = {
        "User-Agent": USER_AGENT,
        "Cache-Control": "no-cache",
    }
    attempts = len(HTTP_RETRY_BACKOFF_SECONDS) + 1
    for attempt in range(attempts):
        req = urllib.request.Request(url, headers=headers, method="GET")
        try:
            with opener.open(req, timeout=HTTP_TIMEOUT_SECONDS) as resp:
                data = resp.read(max_bytes + 1)
                if len(data) > max_bytes:
                    raise ValueError(
                        f"response from {url} exceeded {max_bytes} bytes"
                    )
                return resp.status, data
        except urllib.error.HTTPError as err:
            if err.code == 404:
                return 404, b""
            if err.code in (429, 500, 502, 503, 504) and (
                attempt + 1 < attempts
            ):
                sleep_fn(HTTP_RETRY_BACKOFF_SECONDS[attempt])
                continue
            raise ValueError(f"HTTP {err.code} fetching {url}") from err
        except (
            urllib.error.URLError,
            TimeoutError,
            http.client.HTTPException,
        ) as err:
            if attempt + 1 < attempts:
                sleep_fn(HTTP_RETRY_BACKOFF_SECONDS[attempt])
                continue
            raise ValueError(f"network error fetching {url}: {err}") from err
    raise AssertionError("unreachable")


def _git_output(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        [
            "git",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "core.fsmonitor=false",
            *args,
        ],
        cwd=repo,
        text=True,
        stderr=subprocess.PIPE,
    ).strip()


def _git_is_ancestor(repo: Path, ancestor: str, descendant: str) -> bool:
    result = subprocess.run(
        [
            "git",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "core.fsmonitor=false",
            "merge-base",
            "--is-ancestor",
            ancestor,
            descendant,
        ],
        cwd=repo,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode == 0:
        return True
    if result.returncode == 1:
        return False
    raise ValueError(
        f"git merge-base --is-ancestor failed: {result.stderr.strip()}"
    )


def _fetch_origin_refs(repo: Path) -> None:
    env = {**os.environ, "GIT_TERMINAL_PROMPT": "0"}
    subprocess.run(
        [
            "git",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "core.fsmonitor=false",
            "fetch",
            "--force",
            "origin",
            "+refs/heads/main:refs/remotes/origin/main",
            "+refs/tags/anneal-*:refs/tags/anneal-*",
        ],
        cwd=repo,
        env=env,
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )


def _fetch_crates_io_versions(
    get_bytes: Callable[[str], tuple[int, bytes]],
) -> list[dict[str, object]]:
    """Fetch and validate `versions[]` records for `cargo-anneal`."""
    status, body = get_bytes(CRATES_API_URL)
    if status == 404:
        return []
    if status != 200:
        raise ValueError(f"crates.io API returned HTTP {status}")
    try:
        payload = json.loads(body.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as err:
        raise ValueError(f"invalid crates.io JSON response: {err}") from err
    if not isinstance(payload, dict) or not isinstance(
        payload.get("versions"), list
    ):
        raise ValueError("crates.io response missing versions[] list")
    crate_versions = payload["versions"]
    for entry in crate_versions:
        if not isinstance(entry, dict) or not isinstance(
            entry.get("num"), str
        ):
            raise ValueError("invalid version entry in crates.io response")
        if not isinstance(entry.get("yanked"), bool):
            raise ValueError("invalid yanked flag in crates.io response")
    return crate_versions


def resolve_and_validate(
    repo: Path,
    *,
    version: str,
    commit: str = "",
    default_sha: str,
    expected_sha256: str | None = None,
    expected_source_sha256: str | None = None,
    wait_for_prior_tags_seconds: int = 0,
    http_get: Callable[[str], tuple[int, bytes]] | None = None,
    fetch_refs: Callable[[Path], None] = _fetch_origin_refs,
    clock: Callable[[], float] = time.monotonic,
    sleep_fn: Callable[[float], None] = time.sleep,
) -> ResolvedRelease:
    """Resolve target commit `C` and validate Git + crates.io release state."""
    if not repo.is_dir():
        raise ValueError(f"missing repository directory: {repo}")
    new_semver = parse_anneal_prerelease_version(version)
    validate_commit_sha(default_sha, label="default_sha")
    explicit_commit = (
        validate_commit_sha(commit, label="commit") if commit else None
    )
    exp_sha256 = (
        validate_nonzero_sha256(expected_sha256, label="expected_sha256")
        if expected_sha256 is not None
        else None
    )
    exp_source_sha256 = (
        validate_nonzero_sha256(
            expected_source_sha256, label="expected_source_sha256"
        )
        if expected_source_sha256 is not None
        else None
    )
    if wait_for_prior_tags_seconds < 0:
        raise ValueError("wait_for_prior_tags_seconds must be non-negative")

    get_bytes = http_get or (
        lambda url: _http_get_bytes(url, sleep_fn=sleep_fn)
    )
    deadline = clock() + float(wait_for_prior_tags_seconds)
    release_tag = f"anneal-v{version}"

    while True:
        try:
            main_tip_sha = _git_output(
                repo,
                "rev-parse",
                "--verify",
                "refs/remotes/origin/main^{commit}",
            )
        except subprocess.CalledProcessError as err:
            raise ValueError(
                "missing refs/remotes/origin/main; fetch origin/main first"
            ) from err
        validate_commit_sha(main_tip_sha, label="origin/main")
        try:
            release_notes.ensure_not_shallow(repo, main_tip_sha)
        except (RuntimeError, ValueError, SystemExit) as err:
            raise ValueError(f"shallow repository clone: {err}") from err

        first_parent_commits = set(
            _git_output(
                repo, "rev-list", "--first-parent", "refs/remotes/origin/main"
            ).splitlines()
        )

        raw_tags = _git_output(
            repo,
            "for-each-ref",
            "--format=%(refname:lstrip=2)",
            "refs/tags/anneal-v*",
        )
        git_tags: dict[str, tuple[object, str]] = {}
        for tag_name in raw_tags.splitlines():
            if not tag_name:
                continue
            try:
                t_prefix, t_semver = release_notes.parse_tag(tag_name)
            except (ValueError, SystemExit) as err:
                raise ValueError(
                    f"malformed existing Git tag {tag_name!r}: {err}"
                ) from err
            if t_prefix != "anneal-v":
                raise ValueError(
                    f"unexpected tag prefix on {tag_name!r}: {t_prefix!r}"
                )
            tag_sha = _git_output(
                repo,
                "rev-parse",
                "--verify",
                f"refs/tags/{tag_name}^{{commit}}",
            )
            validate_commit_sha(tag_sha, label=f"tag {tag_name}")
            if tag_sha not in first_parent_commits:
                raise ValueError(
                    f"existing tag {tag_name} ({tag_sha}) is not on "
                    "origin/main first-parent history"
                )
            git_tags[tag_name] = (t_semver, tag_sha)

        max_git_tag_semver = None
        for tag_name, (t_semver, _) in git_tags.items():
            if tag_name == release_tag:
                continue
            if not t_semver.precedence_lt(new_semver):
                raise ValueError(
                    f"version {version} does not strictly exceed existing "
                    f"Git tag {tag_name}"
                )
            if max_git_tag_semver is None or max_git_tag_semver.precedence_lt(
                t_semver
            ):
                max_git_tag_semver = t_semver

        crate_versions = _fetch_crates_io_versions(get_bytes)

        matching_entries = []
        other_entries: list[tuple[dict, object]] = []
        for entry in crate_versions:
            num = entry["num"]
            if num == version:
                matching_entries.append(entry)
                continue
            try:
                c_prefix, c_semver = release_notes.parse_tag(f"anneal-v{num}")
            except (ValueError, SystemExit) as err:
                raise ValueError(
                    f"malformed crates.io version {num!r}: {err}"
                ) from err
            if c_prefix != "anneal-v":
                raise ValueError(f"unexpected crates.io version {num!r}")
            if not c_semver.precedence_lt(new_semver):
                raise ValueError(
                    f"version {version} does not strictly exceed published "
                    f"crates.io version {num}"
                )
            other_entries.append((entry, c_semver))

        if len(matching_entries) > 1:
            raise ValueError(
                f"duplicate crates.io entries for cargo-anneal {version}"
            )

        if not matching_entries:
            if release_tag in git_tags:
                raise ValueError(
                    f"Git tag {release_tag} already exists while {version} "
                    "is absent from crates.io"
                )
            untagged_active_priors = [
                entry["num"]
                for entry, c_semver in other_entries
                if not entry["yanked"]
                and f"anneal-v{entry['num']}" not in git_tags
                and (
                    max_git_tag_semver is None
                    or max_git_tag_semver.precedence_lt(c_semver)
                )
            ]
            if untagged_active_priors:
                now = clock()
                if now < deadline:
                    sleep_fn(
                        min(TAG_POLL_INTERVAL_SECONDS, max(0.0, deadline - now))
                    )
                    fetch_refs(repo)
                    continue
                joined = ", ".join(untagged_active_priors)
                raise ValueError(
                    f"un-yanked prior crates.io release(s) {joined} lack "
                    "corresponding anneal-v* Git tags; complete or recover "
                    "the prior GitHub Release first"
                )

            target_commit = explicit_commit or default_sha
            _verify_target_ancestry(
                repo,
                target_commit=target_commit,
                release_tag=release_tag,
                first_parent_commits=first_parent_commits,
                git_tags=git_tags,
            )
            _verify_commit_sentinel(repo, target_commit)
            return ResolvedRelease(
                already_published=False,
                commit=target_commit,
                archive_sha256="",
                toolchain_tag="",
                published_crate_source_sha256="",
            )

        matched = matching_entries[0]
        if matched["yanked"]:
            raise ValueError(
                f"cargo-anneal {version} is yanked on crates.io; "
                "bump to a new version instead of recovering it"
            )
        checksum = matched.get("checksum")
        validate_nonzero_sha256(
            checksum if isinstance(checksum, str) else "",
            label="crates.io checksum",
        )
        encoded_v = urllib.parse.quote(version, safe=".-_")
        crate_url = f"{STATIC_CRATES_PREFIX}/cargo-anneal-{encoded_v}.crate"
        dl_status, crate_bytes = get_bytes(crate_url)
        if dl_status != 200:
            raise ValueError(
                f"HTTP {dl_status} downloading published crate {crate_url}"
            )
        actual_checksum = hashlib.sha256(crate_bytes).hexdigest()
        if actual_checksum != checksum:
            raise ValueError(
                f"downloaded .crate sha256 {actual_checksum} != "
                f"crates.io checksum {checksum}"
            )

        inspected = inspect_crate_archive(
            crate_bytes,
            version=version,
            expected_commit=explicit_commit,
            expected_sha256=exp_sha256,
        )
        if (
            exp_source_sha256 is not None
            and inspected.crate_source_sha256 != exp_source_sha256
        ):
            raise ValueError(
                f"published crate_source_sha256 "
                f"{inspected.crate_source_sha256} != expected "
                f"{exp_source_sha256}"
            )

        try:
            toolchain_tag_sha = _git_output(
                repo,
                "rev-parse",
                "--verify",
                f"refs/tags/{inspected.toolchain_tag}^{{commit}}",
            )
        except subprocess.CalledProcessError as err:
            raise ValueError(
                f"published crate references missing local Git tag "
                f"{inspected.toolchain_tag}"
            ) from err
        if toolchain_tag_sha != inspected.commit:
            raise ValueError(
                f"tag {inspected.toolchain_tag} points to "
                f"{toolchain_tag_sha}, expected {inspected.commit}"
            )

        if release_tag in git_tags and git_tags[release_tag][1] != (
            inspected.commit
        ):
            raise ValueError(
                f"existing {release_tag} points to {git_tags[release_tag][1]}, "
                f"expected {inspected.commit}"
            )

        _verify_target_ancestry(
            repo,
            target_commit=inspected.commit,
            release_tag=release_tag,
            first_parent_commits=first_parent_commits,
            git_tags=git_tags,
        )
        _verify_commit_sentinel(repo, inspected.commit)
        return ResolvedRelease(
            already_published=True,
            commit=inspected.commit,
            archive_sha256=inspected.archive_sha256,
            toolchain_tag=inspected.toolchain_tag,
            published_crate_source_sha256=inspected.crate_source_sha256,
        )


def _verify_target_ancestry(
    repo: Path,
    *,
    target_commit: str,
    release_tag: str,
    first_parent_commits: set[str],
    git_tags: dict[str, tuple[object, str]],
) -> None:
    validate_commit_sha(target_commit, label="target_commit")
    try:
        release_notes.ensure_not_shallow(repo, target_commit)
    except (RuntimeError, ValueError, SystemExit) as err:
        raise ValueError(
            f"shallow target commit {target_commit}: {err}"
        ) from err
    if target_commit not in first_parent_commits:
        raise ValueError(
            f"commit {target_commit} is not on origin/main first-parent history"
        )
    for tag_name, (_, existing_sha) in git_tags.items():
        if tag_name == release_tag:
            continue
        if target_commit == existing_sha:
            raise ValueError(
                f"commit {target_commit} is already tagged as {tag_name}"
            )
        if not _git_is_ancestor(repo, existing_sha, target_commit):
            raise ValueError(
                f"prior tag {tag_name} ({existing_sha}) is not an ancestor "
                f"of target commit {target_commit}"
            )


def _replace_one(text: str, old: str, new: str) -> str:
    if text.count(old) != 1:
        raise ValueError(f"expected exactly one occurrence of {old!r}")
    return text.replace(old, new, 1)


def _validate_unpinned_sentinel(
    manifest_text: str, lock_text: str
) -> tuple[dict[str, object], dict[str, object]]:
    """Verify `Cargo.toml` and `Cargo.lock` hold the unpinned dev sentinel."""
    try:
        before_manifest = tomllib.loads(manifest_text)
    except tomllib.TOMLDecodeError as err:
        raise ValueError(f"invalid {MANIFEST_REL} TOML: {err}") from err
    try:
        before_lock = tomllib.loads(lock_text)
    except tomllib.TOMLDecodeError as err:
        raise ValueError(f"invalid {LOCK_REL} TOML: {err}") from err

    pkg = before_manifest.get("package")
    exo = (
        pkg.get("metadata", {}).get("exocrate")
        if isinstance(pkg, dict)
        and isinstance(pkg.get("metadata"), dict)
        else None
    )
    if (
        not isinstance(pkg, dict)
        or pkg.get("name") != "cargo-anneal"
        or pkg.get("version") != DEV_VERSION
        or exo
        != [
            {
                "os": "linux",
                "arch": "x86_64",
                "sha256": UNPINNED,
                "url": "",
            }
        ]
        or manifest_text.count(f'version = "{DEV_VERSION}"') != 1
        or manifest_text.count(f'sha256 = "{UNPINNED}"') != 1
        or manifest_text.count('url = ""') != 1
    ):
        raise ValueError(
            f"{MANIFEST_REL} does not hold the expected {DEV_VERSION} "
            "unpinned sentinel metadata"
        )

    raw_packages = before_lock.get("package", [])
    cargo_anneal_locks = (
        [
            entry
            for entry in raw_packages
            if isinstance(entry, dict) and entry.get("name") == "cargo-anneal"
        ]
        if isinstance(raw_packages, list)
        else []
    )
    if (
        len(cargo_anneal_locks) != 1
        or cargo_anneal_locks[0].get("version") != DEV_VERSION
        or lock_text.count(f'{LOCK_ENTRY_PREFIX}"{DEV_VERSION}"') != 1
    ):
        raise ValueError(
            f"{LOCK_REL} does not hold version = {DEV_VERSION!r} for "
            "cargo-anneal"
        )
    return before_manifest, before_lock


def _read_commit_regular_file_text(
    repo: Path, commit: str, rel: Path
) -> str:
    """Read a regular-file blob from `commit`, rejecting symlinks/missing."""
    rel_posix = rel.as_posix()
    ls_out = subprocess.check_output(
        [
            "git",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "core.fsmonitor=false",
            "ls-tree",
            "-z",
            commit,
            "--",
            rel_posix,
        ],
        cwd=repo,
    )
    entries = [entry for entry in ls_out.split(b"\x00") if entry]
    if len(entries) != 1:
        raise ValueError(
            f"commit {commit} does not contain regular file {rel_posix}"
        )
    header_bytes, _, path_bytes = entries[0].partition(b"\t")
    parts = header_bytes.decode("ascii").split(" ")
    if len(parts) != 3 or path_bytes.decode("utf-8", errors="strict") != rel_posix:
        raise ValueError(f"malformed git ls-tree entry for {rel_posix}")
    mode, obj_type, obj_id = parts
    if obj_type != "blob" or mode not in ("100644", "100755"):
        raise ValueError(
            f"commit {commit} entry {rel_posix} must be a regular file "
            f"(got {obj_type} mode {mode})"
        )
    blob = subprocess.check_output(
        [
            "git",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "core.fsmonitor=false",
            "cat-file",
            "blob",
            obj_id,
        ],
        cwd=repo,
    )
    try:
        return blob.decode("utf-8", errors="strict")
    except UnicodeDecodeError as err:
        raise ValueError(
            f"commit {commit} {rel_posix} is not valid UTF-8: {err}"
        ) from err


def _verify_commit_sentinel(repo: Path, commit: str) -> None:
    """Reject target commits missing the unpinned `0.0.0-dev` sentinel."""
    manifest_text = _read_commit_regular_file_text(repo, commit, MANIFEST_REL)
    lock_text = _read_commit_regular_file_text(repo, commit, LOCK_REL)
    _validate_unpinned_sentinel(manifest_text, lock_text)


def stamp_manifests(
    repo: Path, *, version: str, commit: str, sha256: str
) -> tuple[str, str]:
    """Stamp `(version, sha256, url)` into a clean detached `HEAD == commit`."""
    parse_anneal_prerelease_version(version)
    tag, url = toolchain_tag_and_url(commit, sha256)

    head = _git_output(repo, "rev-parse", "HEAD")
    if head != commit:
        raise ValueError(f"HEAD is {head}, expected {commit}")
    dirty_before = _git_output(
        repo, "status", "--porcelain", "--untracked-files=all"
    )
    if dirty_before:
        raise ValueError("stamp requires a clean checkout before stamping")

    manifest_path = repo / MANIFEST_REL
    lock_path = repo / LOCK_REL
    manifest_text = manifest_path.read_text(encoding="utf-8")
    lock_text = lock_path.read_text(encoding="utf-8")

    before_manifest, before_lock = _validate_unpinned_sentinel(
        manifest_text, lock_text
    )

    updated_manifest = _replace_one(
        manifest_text, f'version = "{DEV_VERSION}"', f'version = "{version}"'
    )
    updated_manifest = _replace_one(
        updated_manifest, f'sha256 = "{UNPINNED}"', f'sha256 = "{sha256}"'
    )
    updated_manifest = _replace_one(
        updated_manifest, 'url = ""', f'url = "{url}"'
    )

    updated_lock = _replace_one(
        lock_text,
        f'{LOCK_ENTRY_PREFIX}"{DEV_VERSION}"',
        f'{LOCK_ENTRY_PREFIX}"{version}"',
    )

    after_manifest = tomllib.loads(updated_manifest)
    after_lock = tomllib.loads(updated_lock)

    expected_manifest = deepcopy(before_manifest)
    expected_manifest["package"]["version"] = version
    expected_manifest["package"]["metadata"]["exocrate"][0]["sha256"] = sha256
    expected_manifest["package"]["metadata"]["exocrate"][0]["url"] = url
    if after_manifest != expected_manifest:
        raise ValueError("stamped Cargo.toml AST diverged unexpectedly")

    expected_lock = deepcopy(before_lock)
    for entry in expected_lock["package"]:
        if entry.get("name") == "cargo-anneal":
            entry["version"] = version
    if after_lock != expected_lock:
        raise ValueError("stamped Cargo.lock AST diverged unexpectedly")

    manifest_path.write_text(updated_manifest, encoding="utf-8")
    lock_path.write_text(updated_lock, encoding="utf-8")

    porcelain = subprocess.check_output(
        [
            "git",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "core.fsmonitor=false",
            "status",
            "--porcelain",
            "--untracked-files=all",
        ],
        cwd=repo,
        text=True,
    ).splitlines()
    expected_dirty = {
        f" M {LOCK_REL.as_posix()}",
        f" M {MANIFEST_REL.as_posix()}",
    }
    if set(porcelain) != expected_dirty or len(porcelain) != 2:
        raise ValueError(f"unexpected dirty paths after stamp: {porcelain!r}")

    # Run the harness checkout's non-stable version guard against the stamped
    # target manifest so stamping never executes scripts from a historical `C`.
    check_script = REPO / NON_STABLE_CHECK_REL
    subprocess.run(
        [str(check_script), str(manifest_path.resolve())],
        cwd=REPO,
        check=True,
        capture_output=True,
        text=True,
    )
    return tag, url


def verify_crate_file(
    crate_path: Path,
    *,
    version: str,
    commit: str,
    sha256: str,
    expected_source_sha256: str | None = None,
) -> str:
    """Verify `crate_path` on disk and return `crate_source_sha256`."""
    exp_source = (
        validate_nonzero_sha256(
            expected_source_sha256, label="expected_source_sha256"
        )
        if expected_source_sha256 is not None
        else None
    )
    if not crate_path.is_file():
        raise ValueError(f"missing .crate file: {crate_path}")
    size = crate_path.stat().st_size
    if size > MAX_COMPRESSED_CRATE_BYTES:
        raise ValueError("compressed .crate exceeds 16 MiB limit")
    raw_bytes = crate_path.read_bytes()
    inspected = inspect_crate_archive(
        raw_bytes,
        version=version,
        expected_commit=commit,
        expected_sha256=sha256,
    )
    if exp_source is not None and inspected.crate_source_sha256 != exp_source:
        raise ValueError(
            f"crate_source_sha256 {inspected.crate_source_sha256} != "
            f"expected {exp_source}"
        )
    return inspected.crate_source_sha256


def verify_published_crate(
    crate_path: Path,
    *,
    version: str,
    commit: str,
    sha256: str,
    expected_source_sha256: str,
    wait_seconds: int = 120,
    http_get: Callable[[str], tuple[int, bytes]] | None = None,
    sleep_fn: Callable[[float], None] = time.sleep,
    clock: Callable[[], float] = time.monotonic,
) -> str:
    """Verify `.crate` parity after publish and confirm crates.io checksum."""
    if wait_seconds < 0:
        raise ValueError("wait_seconds must be non-negative")
    source_sha256 = verify_crate_file(
        crate_path,
        version=version,
        commit=commit,
        sha256=sha256,
        expected_source_sha256=expected_source_sha256,
    )
    local_crate_sha256 = hashlib.sha256(crate_path.read_bytes()).hexdigest()
    get_bytes = http_get or (
        lambda url: _http_get_bytes(url, sleep_fn=sleep_fn)
    )
    deadline = clock() + float(wait_seconds)
    while True:
        crate_versions = _fetch_crates_io_versions(get_bytes)
        matching = [
            entry for entry in crate_versions if entry["num"] == version
        ]
        if len(matching) > 1:
            raise ValueError(
                f"duplicate crates.io entries for cargo-anneal {version}"
            )
        if matching:
            matched = matching[0]
            if matched["yanked"]:
                raise ValueError(
                    f"published cargo-anneal {version} is unexpectedly yanked"
                )
            checksum = matched.get("checksum")
            validate_nonzero_sha256(
                checksum if isinstance(checksum, str) else "",
                label="crates.io checksum",
            )
            if checksum != local_crate_sha256:
                raise ValueError(
                    f"crates.io checksum {checksum} != local published "
                    f".crate sha256 {local_crate_sha256}"
                )
            return source_sha256
        now = clock()
        if now >= deadline:
            raise ValueError(
                f"cargo-anneal {version} not visible on crates.io within "
                f"{wait_seconds}s"
            )
        sleep_fn(min(TAG_POLL_INTERVAL_SECONDS, max(0.0, deadline - now)))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="subcommand", required=True)

    resolve_cmd = sub.add_parser(
        "resolve-and-validate",
        help="Validate version ordering and resolve target main commit.",
    )
    resolve_cmd.add_argument("--repo", type=Path, default=REPO)
    resolve_cmd.add_argument("--version", required=True)
    resolve_cmd.add_argument("--commit", default="")
    resolve_cmd.add_argument("--default-sha", required=True)
    resolve_cmd.add_argument("--expected-sha256", default=None)
    resolve_cmd.add_argument("--expected-source-sha256", default=None)
    resolve_cmd.add_argument(
        "--wait-for-prior-tags-seconds", type=int, default=0
    )

    tag_cmd = sub.add_parser(
        "toolchain-tag",
        help="Compute the commit-and-digest-addressed toolchain tag and URL.",
    )
    tag_cmd.add_argument("--commit", required=True)
    tag_cmd.add_argument("--sha256", required=True)

    stamp_cmd = sub.add_parser(
        "stamp",
        help="Stamp Cargo.toml and Cargo.lock in-place on a detached checkout.",
    )
    stamp_cmd.add_argument("--repo", type=Path, default=REPO)
    stamp_cmd.add_argument("--version", required=True)
    stamp_cmd.add_argument("--commit", required=True)
    stamp_cmd.add_argument("--sha256", required=True)

    verify_cmd = sub.add_parser(
        "verify-crate",
        help="Verify a packaged .crate archive and print its source hash.",
    )
    verify_cmd.add_argument("--crate", required=True, type=Path)
    verify_cmd.add_argument("--version", required=True)
    verify_cmd.add_argument("--commit", required=True)
    verify_cmd.add_argument("--sha256", required=True)
    verify_cmd.add_argument("--expected-source-sha256", default=None)

    verify_pub_cmd = sub.add_parser(
        "verify-published-crate",
        help="Verify published .crate source parity and crates.io checksum.",
    )
    verify_pub_cmd.add_argument("--crate", required=True, type=Path)
    verify_pub_cmd.add_argument("--version", required=True)
    verify_pub_cmd.add_argument("--commit", required=True)
    verify_pub_cmd.add_argument("--sha256", required=True)
    verify_pub_cmd.add_argument("--expected-source-sha256", required=True)
    verify_pub_cmd.add_argument("--wait-seconds", type=int, default=120)

    return parser


def main(argv: list[str] | None = None) -> None:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        if args.subcommand == "resolve-and-validate":
            resolved = resolve_and_validate(
                args.repo.resolve(),
                version=args.version,
                commit=args.commit,
                default_sha=args.default_sha,
                expected_sha256=args.expected_sha256,
                expected_source_sha256=args.expected_source_sha256,
                wait_for_prior_tags_seconds=args.wait_for_prior_tags_seconds,
            )
            sys.stdout.write(resolved.format_github_output())
            return
        if args.subcommand == "toolchain-tag":
            tag, url = toolchain_tag_and_url(args.commit, args.sha256)
            sys.stdout.write(f"tag={tag}\nurl={url}\n")
            return
        if args.subcommand == "stamp":
            stamp_manifests(
                args.repo.resolve(),
                version=args.version,
                commit=args.commit,
                sha256=args.sha256,
            )
            return
        if args.subcommand == "verify-crate":
            source_sha256 = verify_crate_file(
                args.crate,
                version=args.version,
                commit=args.commit,
                sha256=args.sha256,
                expected_source_sha256=args.expected_source_sha256,
            )
            sys.stdout.write(f"{source_sha256}\n")
            return
        if args.subcommand == "verify-published-crate":
            source_sha256 = verify_published_crate(
                args.crate,
                version=args.version,
                commit=args.commit,
                sha256=args.sha256,
                expected_source_sha256=args.expected_source_sha256,
                wait_seconds=args.wait_seconds,
            )
            sys.stdout.write(f"{source_sha256}\n")
            return
    except (ValueError, RuntimeError, subprocess.CalledProcessError) as err:
        detail = err.stderr.strip() if isinstance(
            err, subprocess.CalledProcessError
        ) and err.stderr else str(err)
        parser.exit(1, f"error: {detail}\n")


if __name__ == "__main__":
    main()
