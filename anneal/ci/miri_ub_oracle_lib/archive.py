# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Pinned archive download, SHA-256 verification, and streaming extraction
of the Miri corpus."""

from __future__ import annotations

import errno
import gzip
import hashlib
import hmac
import os
from pathlib import Path, PurePosixPath
import stat
import tarfile
import time
import urllib.parse
import urllib.request
import zlib

from .common import (
    DOWNLOAD_CHUNK_BYTES, HEX40_RE, MAX_ARCHIVE_BYTES, MAX_DECOMPRESSED_TAR_BYTES,
    MAX_SINGLE_FILE_BYTES, MAX_TAR_MEMBERS, MAX_TOTAL_EXTRACTED_BYTES, OracleError,
)
from .pins import (
    _PinnedHttpsRedirectHandler, _fetch_pinned_github_json, _resolve_github_subtree_sha,
    _validate_https_host,
)


def verify_rustc_miri_linkage(
    pin: dict[str, object], *, timeout_secs: float = 30.0
) -> None:
    """Verify upstream `rust-lang/rust@rustc_commit` matches `miri_commit` trees.

    Uses only documented 40-char SHA Git Data API endpoints (`/git/commits/{sha}`
    and `/git/trees/{sha}`) over pinned HTTPS `api.github.com` to confirm:
    1. Walking `src/tools/miri` from `rust-lang/rust@<rustc_commit>`'s root
       tree yields `pin["miri_tree_sha"]`.
    2. Walking `tests/fail` (and `tests/fail-dep` when configured) under that
       subtree matches `pin["fail_tree_sha"]` (and `pin["fail_dep_tree_sha"]`).
    3. `rust-lang/miri@<miri_commit>`'s commit root tree SHA equals
       `pin["miri_tree_sha"]`, cryptographically binding the Miri pin to the
       pinned `rustc_commit` subtree.
    """
    rustc_commit = str(pin["rustc_commit"])
    miri_commit = str(pin["miri_commit"])
    expected_miri_tree = str(pin["miri_tree_sha"])
    subdirs = set(pin["extract_subdirs"])  # type: ignore[arg-type]
    deadline = time.monotonic() + timeout_secs

    rustc_commit_obj = _fetch_pinned_github_json(
        f"https://api.github.com/repos/rust-lang/rust/git/commits/{rustc_commit}",
        deadline=deadline,
    )
    rustc_tree_meta = rustc_commit_obj.get("tree")
    rustc_root_sha = (
        rustc_tree_meta.get("sha") if isinstance(rustc_tree_meta, dict) else None
    )
    if not isinstance(rustc_root_sha, str) or not HEX40_RE.fullmatch(rustc_root_sha):
        raise OracleError(
            f"rust-lang/rust@{rustc_commit} git commit missing valid root tree SHA"
        )

    actual_rustc_miri_sha = _resolve_github_subtree_sha(
        "rust-lang/rust", rustc_root_sha, ("src", "tools", "miri"), deadline=deadline
    )
    if not hmac.compare_digest(actual_rustc_miri_sha, expected_miri_tree):
        raise OracleError(
            f"rust-lang/rust@{rustc_commit}:src/tools/miri tree SHA mismatch: "
            f"expected {expected_miri_tree}, got {actual_rustc_miri_sha!r}"
        )

    tests_tree_sha = _resolve_github_subtree_sha(
        "rust-lang/rust", actual_rustc_miri_sha, ("tests",), deadline=deadline
    )
    expected_subtrees: list[tuple[str, str]] = [("fail", str(pin["fail_tree_sha"]))]
    if "tests/fail-dep" in subdirs:
        expected_subtrees.append(("fail-dep", str(pin["fail_dep_tree_sha"])))
    for sub_name, expected_sha in expected_subtrees:
        actual_sub = _resolve_github_subtree_sha(
            "rust-lang/rust", tests_tree_sha, (sub_name,), deadline=deadline
        )
        if not hmac.compare_digest(actual_sub, expected_sha):
            raise OracleError(
                f"rust-lang/rust@{rustc_commit}:src/tools/miri/tests/{sub_name} "
                f"tree SHA mismatch: expected {expected_sha}, got {actual_sub!r}"
            )

    miri_commit_obj = _fetch_pinned_github_json(
        f"https://api.github.com/repos/rust-lang/miri/git/commits/{miri_commit}",
        deadline=deadline,
    )
    miri_tree_meta = miri_commit_obj.get("tree")
    actual_miri_root_sha = (
        miri_tree_meta.get("sha") if isinstance(miri_tree_meta, dict) else None
    )
    if not isinstance(actual_miri_root_sha, str) or not hmac.compare_digest(
        actual_miri_root_sha, expected_miri_tree
    ):
        raise OracleError(
            f"rust-lang/miri@{miri_commit} root tree SHA mismatch against "
            f"rust-lang/rust@{rustc_commit}:src/tools/miri: "
            f"expected {expected_miri_tree}, got {actual_miri_root_sha!r}"
        )


def copy_and_verify_archive_sha256(
    src_path: Path,
    dest_path: Path,
    expected_sha256: str,
    *,
    max_bytes: int = MAX_ARCHIVE_BYTES,
) -> str:
    """Copy a local archive into a private temp file while verifying SHA-256.

    Opens `src_path` once with `O_NOFOLLOW | O_NONBLOCK`, validates `fstat`
    on the resulting descriptor (rejecting symlinks and special files such as
    FIFOs without blocking or check-then-open TOCTOU), and hashes while copying
    so verification and extraction see identical bytes.
    """
    flags = (
        os.O_RDONLY
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    try:
        fd = os.open(src_path, flags)
    except OSError as exc:
        if exc.errno == errno.ELOOP:
            raise OracleError(
                f"archive path must be a regular non-symlink file: {src_path}"
            ) from exc
        raise OracleError(
            f"failed opening archive '{src_path}': {exc}"
        ) from exc

    hasher = hashlib.sha256()
    total = 0
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise OracleError(
                f"archive path must be a regular non-symlink file: {src_path}"
            )
        if st.st_size > max_bytes:
            raise OracleError(
                f"archive '{src_path}' exceeds max allowed size ({max_bytes} B)"
            )
        with (
            os.fdopen(fd, "rb", closefd=False) as inp,
            dest_path.open("wb") as out,
        ):
            while True:
                chunk = inp.read(DOWNLOAD_CHUNK_BYTES)
                if not chunk:
                    break
                total += len(chunk)
                if total > max_bytes:
                    raise OracleError(
                        f"archive '{src_path}' exceeds max allowed size "
                        f"({max_bytes} B)"
                    )
                hasher.update(chunk)
                out.write(chunk)
    except OracleError:
        dest_path.unlink(missing_ok=True)
        raise
    except OSError as exc:
        dest_path.unlink(missing_ok=True)
        raise OracleError(f"failed reading archive '{src_path}': {exc}") from exc
    finally:
        os.close(fd)

    actual = hasher.hexdigest()
    if not hmac.compare_digest(actual, expected_sha256):
        dest_path.unlink(missing_ok=True)
        raise OracleError(
            f"archive SHA-256 mismatch for '{src_path}': "
            f"expected {expected_sha256}, got {actual}"
        )
    return actual


def download_verified_archive(
    url: str,
    expected_sha256: str,
    dest_path: Path,
    *,
    timeout_secs: float = 60.0,
    max_bytes: int = MAX_ARCHIVE_BYTES,
) -> str:
    """Download an archive over HTTPS, enforcing host, size, and SHA-256."""
    _validate_https_host(url)
    opener = urllib.request.build_opener(_PinnedHttpsRedirectHandler())
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "anneal-miri-ub-oracle/1"},
    )
    hasher = hashlib.sha256()
    total = 0
    deadline = time.monotonic() + timeout_secs
    try:
        with opener.open(req, timeout=timeout_secs) as resp:
            _validate_https_host(resp.geturl())
            with dest_path.open("wb") as out:
                while True:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        raise OracleError(
                            f"archive download exceeded {timeout_secs:.1f}s "
                            "wall-clock deadline"
                        )
                    raw_sock = getattr(getattr(resp, "fp", None), "raw", None)
                    sock = getattr(raw_sock, "_sock", None)
                    if sock is not None and hasattr(sock, "settimeout"):
                        sock.settimeout(remaining)
                    chunk = resp.read(DOWNLOAD_CHUNK_BYTES)
                    if time.monotonic() > deadline:
                        raise OracleError(
                            f"archive download exceeded {timeout_secs:.1f}s "
                            "wall-clock deadline"
                        )
                    if not chunk:
                        break
                    total += len(chunk)
                    if total > max_bytes:
                        raise OracleError(
                            f"downloaded archive exceeds {max_bytes} B ceiling"
                        )
                    hasher.update(chunk)
                    out.write(chunk)
    except OracleError:
        dest_path.unlink(missing_ok=True)
        raise
    except Exception as exc:
        dest_path.unlink(missing_ok=True)
        raise OracleError(f"failed to download '{url}': {exc}") from exc

    actual = hasher.hexdigest()
    if not hmac.compare_digest(actual, expected_sha256):
        dest_path.unlink(missing_ok=True)
        raise OracleError(
            f"downloaded archive SHA-256 mismatch: "
            f"expected {expected_sha256}, got {actual}"
        )
    return actual


def _validate_tar_member_path(raw_name: str, expected_top_dir: str) -> PurePosixPath:
    """Reject path traversal, absolute paths, Windows drives, and bad roots."""
    if not raw_name:
        raise OracleError("tar archive contains empty member name")
    if "\x00" in raw_name or "\\" in raw_name:
        raise OracleError(f"tar member contains forbidden character: {raw_name!r}")
    if raw_name.startswith("/") or raw_name.startswith("~"):
        raise OracleError(f"tar member has absolute or home path: {raw_name!r}")

    parts = raw_name.split("/")
    # GitHub tarballs include a trailing '/' on directory entries.
    if parts and parts[-1] == "":
        parts = parts[:-1]
    if not parts:
        raise OracleError(f"tar member normalizes to empty path: {raw_name!r}")
    for seg in parts:
        if seg in ("", ".", "..") or ":" in seg:
            raise OracleError(
                f"tar member contains forbidden path segment {seg!r}: {raw_name!r}"
            )
    if parts[0] != expected_top_dir:
        raise OracleError(
            f"tar member escapes expected top dir '{expected_top_dir}': {raw_name!r}"
        )
    return PurePosixPath(*parts)


def _compute_git_tree_sha1(tree_node: dict[str, object]) -> bytes:
    """Compute canonical Git tree SHA-1 (raw 20-byte digest) for a tree dict."""
    items: list[tuple[bytes, bytes, bytes, bytes]] = []
    for name, val in tree_node.items():
        name_bytes = name.encode("utf-8")
        if isinstance(val, dict):
            sub_sha = _compute_git_tree_sha1(val)
            items.append((name_bytes + b"/", b"40000", name_bytes, sub_sha))
        else:
            mode, blob_sha = val  # type: ignore[misc]
            items.append((name_bytes, mode, name_bytes, blob_sha))
    items.sort(key=lambda entry: entry[0])
    payload = b"".join(
        mode + b" " + name_b + b"\x00" + sha for _, mode, name_b, sha in items
    )
    header = f"tree {len(payload)}\x00".encode("ascii")
    return hashlib.sha1(header + payload).digest()


def _expected_archive_tree_shas(pin: dict[str, object]) -> dict[str, str]:
    expected = {"": str(pin["miri_tree_sha"])}
    subdirs = set(pin["extract_subdirs"])  # type: ignore[arg-type]
    if "tests/fail" in subdirs:
        expected["tests/fail"] = str(pin["fail_tree_sha"])
    if "tests/fail-dep" in subdirs:
        expected["tests/fail-dep"] = str(pin["fail_dep_tree_sha"])
    return expected


class _BoundedReadStream:
    """Read-only wrapper enforcing a hard decompressed byte ceiling.

    Bounds the raw stream fed to `tarfile.open(..., mode="r|")` so oversized
    compressed PAX or GNU extended headers fail closed before `tarfile` can
    materialize unbounded metadata in memory.
    """

    def __init__(self, inner: object, max_bytes: int) -> None:
        self._inner = inner
        self._max_bytes = max_bytes
        self._total = 0

    def read(self, size: int = -1) -> bytes:
        remaining = self._max_bytes - self._total
        if size is None or size < 0 or size > remaining + 1:
            to_read = remaining + 1
        else:
            to_read = size
        data: bytes = self._inner.read(to_read)  # type: ignore[attr-defined]
        self._total += len(data)
        if self._total > self._max_bytes:
            raise OracleError(
                f"decompressed tar stream exceeds {self._max_bytes} B cap"
            )
        return data


def safe_extract_miri_corpus(
    archive_path: Path,
    dest_dir: Path,
    *,
    expected_top_dir: str,
    extract_subdirs: list[str],
    expected_tree_shas: dict[str, str] | None = None,
) -> list[str]:
    """Safely extract `tests/fail*/*.rs` without ever calling `extractall`.

    Every member in the tarball is inspected for symlinks, hardlinks, device
    nodes, and path traversal before extracting the requested `.rs` files.
    When `expected_tree_shas` is supplied, recomputes exact Git tree SHA-1
    digests from the streamed archive members and fails closed on mismatch.
    """
    dest_root = dest_dir.resolve()
    dest_root.mkdir(parents=True, exist_ok=True)
    subdir_prefixes = tuple(s.rstrip("/") + "/" for s in extract_subdirs)

    extracted_relpaths: set[str] = set()
    seen_archive_files: set[str] = set()
    git_tree_root: dict[str, object] = {}
    total_extracted_bytes = 0

    try:
        with (
            archive_path.open("rb") as raw_fh,
            gzip.GzipFile(fileobj=raw_fh, mode="rb") as gz_fh,
            tarfile.open(
                fileobj=_BoundedReadStream(gz_fh, MAX_DECOMPRESSED_TAR_BYTES),
                mode="r|",
            ) as tf,
        ):
            member_count = 0
            while True:
                member = tf.next()
                if member is None:
                    break
                member_count += 1
                if member_count > MAX_TAR_MEMBERS:
                    raise OracleError(
                        f"tar archive exceeds {MAX_TAR_MEMBERS} members "
                        f"(cap {MAX_TAR_MEMBERS})"
                    )
                if (
                    member.issym()
                    or member.islnk()
                    or member.ischr()
                    or member.isblk()
                    or member.isfifo()
                    or member.isdev()
                ):
                    raise OracleError(
                        f"tar archive contains forbidden link/special member: "
                        f"{member.name!r} (type={member.type!r})"
                    )
                if not (member.isfile() or member.isdir()):
                    raise OracleError(
                        f"tar archive contains unsupported member type: "
                        f"{member.name!r} (type={member.type!r})"
                    )
                norm = _validate_tar_member_path(member.name, expected_top_dir)
                if not member.isfile():
                    tf.members.clear()
                    continue
                if len(norm.parts) < 2:
                    tf.members.clear()
                    continue
                inner_parts = norm.parts[1:]
                inner = PurePosixPath(*inner_parts).as_posix()
                if inner in seen_archive_files:
                    raise OracleError(
                        f"tar archive contains duplicate path '{inner}'"
                    )
                seen_archive_files.add(inner)

                is_extract_rs = inner.startswith(subdir_prefixes) and inner.endswith(
                    ".rs"
                )
                need_payload = is_extract_rs or (expected_tree_shas is not None)
                if not need_payload:
                    tf.members.clear()
                    continue

                if member.size < 0 or member.size > MAX_SINGLE_FILE_BYTES:
                    raise OracleError(
                        f"tar member '{inner}' exceeds single-file cap "
                        f"({member.size} > {MAX_SINGLE_FILE_BYTES})"
                    )
                fileobj = tf.extractfile(member)
                if fileobj is None:
                    raise OracleError(f"failed to extract tar member '{inner}'")
                payload = fileobj.read(MAX_SINGLE_FILE_BYTES + 1)
                if len(payload) > MAX_SINGLE_FILE_BYTES or len(payload) != member.size:
                    raise OracleError(
                        f"tar member '{inner}' decompressed size mismatch "
                        f"({len(payload)} vs header {member.size})"
                    )
                total_extracted_bytes += len(payload)
                if total_extracted_bytes > MAX_TOTAL_EXTRACTED_BYTES:
                    raise OracleError(
                        f"extracted corpus exceeds {MAX_TOTAL_EXTRACTED_BYTES} B cap"
                    )

                if expected_tree_shas is not None:
                    blob_header = f"blob {len(payload)}\x00".encode("ascii")
                    blob_sha = hashlib.sha1(blob_header + payload).digest()
                    mode = b"100755" if (member.mode & 0o111) else b"100644"
                    cur_node: dict[str, object] = git_tree_root
                    for seg in inner_parts[:-1]:
                        nxt = cur_node.get(seg)
                        if nxt is None:
                            nxt = {}
                            cur_node[seg] = nxt
                        elif not isinstance(nxt, dict):
                            raise OracleError(
                                f"tar archive path conflict at '{inner}'"
                            )
                        cur_node = nxt
                    if inner_parts[-1] in cur_node:
                        raise OracleError(
                            f"tar archive path conflict at '{inner}'"
                        )
                    cur_node[inner_parts[-1]] = (mode, blob_sha)

                if is_extract_rs:
                    rel_under_tests = inner[len("tests/"):]
                    extracted_relpaths.add(rel_under_tests)
                    dst = (dest_root / rel_under_tests).resolve()
                    try:
                        dst.relative_to(dest_root)
                    except ValueError as exc:
                        raise OracleError(
                            f"extracted path escapes destination root: {dst}"
                        ) from exc
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    with dst.open("xb") as out:
                        out.write(payload)
                tf.members.clear()
    except OracleError:
        raise
    except (tarfile.TarError, OSError, EOFError, zlib.error) as exc:
        raise OracleError(f"failed reading tar archive '{archive_path}': {exc}") from exc

    if expected_tree_shas is not None:
        for subtree_key, expected_sha in sorted(expected_tree_shas.items()):
            node: object = git_tree_root
            if subtree_key:
                for seg in subtree_key.split("/"):
                    if not isinstance(node, dict) or seg not in node:
                        raise OracleError(
                            f"tar archive missing expected subtree '{subtree_key}'"
                        )
                    node = node[seg]
            if not isinstance(node, dict):
                raise OracleError(
                    f"tar archive subtree '{subtree_key}' is not a directory"
                )
            actual_sha = _compute_git_tree_sha1(node).hex()
            if not hmac.compare_digest(actual_sha, expected_sha):
                label = subtree_key or "<root>"
                raise OracleError(
                    f"tar archive Git tree SHA-1 mismatch for '{label}': "
                    f"expected {expected_sha}, got {actual_sha}"
                )

    return sorted(extracted_relpaths)
