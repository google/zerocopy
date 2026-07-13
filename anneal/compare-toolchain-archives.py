#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://opensource.org/licenses/Apache-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Compare the semantic contents of two Anneal toolchain archives.

The fast and slow archive builds can legitimately differ in compression, tar
headers, and the contents of narrowly defined Lake bookkeeping files.  They
must otherwise contain exactly the same payload.  This program therefore
compares SHA-256 hashes and modes for all Lean, Rust, and non-``.lake`` Aeneas
payload files, and for all actual files below every ``.lake/build`` directory.
That includes complete ``.ilean`` code-intelligence data and its hash sidecars.

Lake traces contain contextual command logs and dependency descriptions, so
their raw JSON need not be byte-identical.  Their schema version, dependency
hash, and output hashes are canonicalized and compared.  Response files, setup
JSON, and ``.lake/config`` contents may also be contextual, but their complete
path, type, link-target, and mode inventories must be identical.

Lake artifact archives/caches, no-build markers, and temporary primer state
are rejected outright.  A normal-file versus hard-link representation is
treated as an archive-storage detail when both resolve to identical bytes.

Archives are never extracted to the filesystem.  ``zstd`` streams each archive
into Python's tar reader; member paths and link targets are validated before
regular file contents are inspected.  This avoids following archive-provided
links and avoids path traversal by construction.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tarfile
import tempfile
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import BinaryIO, Iterable


ZSTD_MAGIC = b"\x28\xb5\x2f\xfd"

EXPECTED_TOP_LEVELS = {"aeneas", "lean", "rust"}

REQUIRED_MEMBER_PATHS = {
    "aeneas/bin/aeneas",
    "aeneas/bin/charon",
    "aeneas/bin/charon-driver",
    "aeneas/backends/lean/.lake/config/aeneas/lakefile.olean",
    "aeneas/packages/mathlib/.lake/config/mathlib/lakefile.olean",
    "aeneas/packages/mathlib/lake-manifest.json",
    "lean/bin/lake",
    "lean/bin/lean",
    "rust/bin/cargo",
    "rust/bin/rustc",
}

REQUIRED_EXECUTABLE_PATHS = {
    "aeneas/bin/aeneas",
    "aeneas/bin/charon",
    "aeneas/bin/charon-driver",
    "lean/bin/lake",
    "lean/bin/lean",
    "rust/bin/cargo",
    "rust/bin/rustc",
}

# These are path-bearing command descriptions rather than compiler outputs.
# Their bytes may differ, but their inventory is compared.  Do not add broad
# suffixes such as `.json`: an arbitrary generated JSON file may be a real
# build output.  In particular, every `.hash` sidecar is compiler output and
# is compared exactly. Lake traces are handled separately below: their stable
# dependency and output hashes are semantic even though their logs are not.
INVENTORY_ONLY_BUILD_SUFFIXES = (
    ".rsp",
    ".setup.json",
)

DEFAULT_MAX_MEMBERS = 1_000_000
DEFAULT_MAX_MEMBER_BYTES = 8 * 1024**3
DEFAULT_MAX_ARCHIVE_BYTES = 32 * 1024**3
MAX_CANONICAL_TRACE_BYTES = 512 * 1024**2
COPY_CHUNK_SIZE = 1024 * 1024


class ArchiveInspectionError(RuntimeError):
    """An archive is malformed, unsafe, or not an Anneal toolchain archive."""


@dataclass(frozen=True)
class FileContent:
    sha256: str
    size: int
    canonical_trace: bool = False


@dataclass(frozen=True)
class SemanticRecord:
    """Content, type, and mode relevant to archive equivalence."""

    kind: str
    mode: int
    sha256: str | None = None
    size: int | None = None
    link_target: str | None = None

    def short_description(self) -> str:
        mode = f"mode={self.mode:#06o}"
        if self.kind == "directory":
            return f"directory, {mode}"
        if self.kind == "symlink":
            return f"symlink -> {self.link_target}, {mode}"
        if self.sha256 is None:
            return f"{self.kind}, content ignored, {mode}"
        return f"sha256={self.sha256[:16]}..., {self.size} bytes, {mode}"


@dataclass(frozen=True)
class PendingSemanticFile:
    path: str
    content_path: str
    mode: int
    canonical_trace: bool


@dataclass
class ArchiveInventory:
    semantic_files: dict[str, SemanticRecord]
    metadata_files: dict[str, SemanticRecord]
    ignored_files: Counter[str]
    present_paths: set[str]
    regular_like_paths: set[str]
    top_levels: set[str]
    member_count: int
    declared_file_bytes: int

    def comparison_records(self) -> dict[str, SemanticRecord]:
        records = dict(self.semantic_files)
        overlap = records.keys() & self.metadata_files.keys()
        if overlap:
            raise AssertionError(f"records classified twice: {sorted(overlap)}")
        records.update(self.metadata_files)
        return records


@dataclass(frozen=True)
class ComparisonResult:
    only_first: tuple[str, ...]
    only_second: tuple[str, ...]
    changed: tuple[str, ...]

    @property
    def equivalent(self) -> bool:
        return not (self.only_first or self.only_second or self.changed)


def _normalize_member_name(name: str) -> str:
    if not name or "\x00" in name:
        raise ArchiveInspectionError("archive contains an empty or NUL-containing path")
    if name.startswith("/") or "\\" in name:
        raise ArchiveInspectionError(f"archive contains a non-POSIX or absolute path: {name!r}")

    parts: list[str] = []
    for part in name.split("/"):
        if part in ("", "."):
            continue
        if part == "..":
            raise ArchiveInspectionError(f"archive path contains '..': {name!r}")
        parts.append(part)
    if not parts:
        raise ArchiveInspectionError(f"archive path normalizes to empty: {name!r}")
    return "/".join(parts)


def _normalize_symlink_target(member_path: str, target: str) -> str:
    if not target or "\x00" in target or target.startswith("/") or "\\" in target:
        raise ArchiveInspectionError(
            f"unsafe symlink target for {member_path!r}: {target!r}"
        )

    parts = member_path.split("/")[:-1]
    for part in target.split("/"):
        if part in ("", "."):
            continue
        if part == "..":
            if not parts:
                raise ArchiveInspectionError(
                    f"symlink escapes archive root: {member_path!r} -> {target!r}"
                )
            parts.pop()
        else:
            parts.append(part)
    if not parts:
        raise ArchiveInspectionError(
            f"symlink resolves to archive root: {member_path!r} -> {target!r}"
        )
    return "/".join(parts)


def _lake_directory_kind(path: str) -> str | None:
    parts = path.split("/")
    try:
        index = parts.index(".lake")
    except ValueError:
        return None
    if index + 1 >= len(parts):
        return "state"
    return parts[index + 1]


def _inventory_only_build_category(path: str) -> str | None:
    for suffix in INVENTORY_ONLY_BUILD_SUFFIXES:
        if path.endswith(suffix):
            return {
                ".rsp": "lake-response-file",
                ".setup.json": "lake-setup-json",
            }[suffix]
    return None


def _classify_file(path: str) -> tuple[bool, str]:
    """Return ``(is_semantic, category)`` for a non-directory member."""

    if not path.startswith("aeneas/") and path != "aeneas":
        return True, "toolchain-payload"

    lake_kind = _lake_directory_kind(path)
    if lake_kind is None:
        return True, "aeneas-payload"
    if lake_kind == "build":
        ignored = _inventory_only_build_category(path)
        if ignored is not None:
            return False, ignored
        return True, "lake-build-output"
    if lake_kind == "config":
        return False, "lake-config-cache"
    # Artifact caches are rejected before classification.  Unknown `.lake`
    # state is compared exactly rather than silently widening the exception.
    return True, "lake-other-state"


def _is_lake_build_path(path: str) -> bool:
    return path.startswith("aeneas/") and _lake_directory_kind(path) == "build"


def _is_lake_build_trace(path: str) -> bool:
    return _is_lake_build_path(path) and path.endswith(".trace")


def _canonicalize_trace(data: bytes, path: str) -> bytes:
    try:
        document = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ArchiveInspectionError(f"invalid Lake trace JSON in {path!r}: {error}") from error
    if not isinstance(document, dict):
        raise ArchiveInspectionError(f"Lake trace JSON is not an object: {path!r}")
    for field in ("schemaVersion", "depHash", "outputs"):
        if field not in document:
            raise ArchiveInspectionError(
                f"Lake trace JSON has no {field!r} field: {path!r}"
            )
    canonical_document = {
        field: document[field] for field in ("schemaVersion", "depHash", "outputs")
    }
    try:
        return json.dumps(
            canonical_document,
            ensure_ascii=False,
            allow_nan=False,
            separators=(",", ":"),
            sort_keys=True,
        ).encode("utf-8")
    except (TypeError, ValueError) as error:
        raise ArchiveInspectionError(
            f"cannot canonicalize Lake trace JSON in {path!r}: {error}"
        ) from error


def _hash_stream(
    stream: BinaryIO,
    expected_size: int,
    path: str,
    *,
    canonicalize_trace: bool,
) -> FileContent:
    if canonicalize_trace:
        if expected_size > MAX_CANONICAL_TRACE_BYTES:
            raise ArchiveInspectionError(
                f"Lake trace {path!r} exceeds the canonicalization limit of "
                f"{MAX_CANONICAL_TRACE_BYTES} bytes"
            )
        data = stream.read()
        if len(data) != expected_size:
            raise ArchiveInspectionError(
                f"short archive member {path!r}: header says {expected_size} bytes, "
                f"read {len(data)}"
            )
        canonical = _canonicalize_trace(data, path)
        return FileContent(
            hashlib.sha256(canonical).hexdigest(),
            len(canonical),
            canonical_trace=True,
        )

    digest = hashlib.sha256()
    size = 0
    while True:
        block = stream.read(COPY_CHUNK_SIZE)
        if not block:
            break
        size += len(block)
        digest.update(block)
    if size != expected_size:
        raise ArchiveInspectionError(
            f"short archive member {path!r}: header says {expected_size} bytes, read {size}"
        )
    return FileContent(digest.hexdigest(), size)


def _resolve_content(
    path: str,
    regular_contents: dict[str, FileContent],
    hardlinks: dict[str, str],
    visiting: set[str] | None = None,
) -> FileContent:
    if path in regular_contents:
        return regular_contents[path]
    target = hardlinks.get(path)
    if target is None:
        raise ArchiveInspectionError(
            f"hard link ultimately targets unavailable content: {path!r}"
        )
    visiting = set() if visiting is None else visiting
    if path in visiting:
        raise ArchiveInspectionError(f"hard-link cycle involving {path!r}")
    visiting.add(path)
    try:
        return _resolve_content(target, regular_contents, hardlinks, visiting)
    finally:
        visiting.remove(path)


def _forbidden_state(path: str) -> str | None:
    parts = path.split("/")
    if path.endswith(".ltar"):
        return "Lake artifact archive (.ltar)"
    if path.endswith(".nobuild"):
        return "stale no-build marker (.nobuild)"
    if any(part == ".anneal-tmp" or part.endswith(".anneal-tmp") for part in parts):
        return "temporary primer state (.anneal-tmp)"
    if any(
        part == ".lake" and index + 1 < len(parts) and parts[index + 1] == "cache"
        for index, part in enumerate(parts)
    ):
        return "Lake artifact cache (.lake/cache)"
    return None


def _read_tar_stream(
    stream: BinaryIO,
    *,
    max_members: int,
    max_member_bytes: int,
    max_archive_bytes: int,
) -> ArchiveInventory:
    semantic_files: dict[str, SemanticRecord] = {}
    metadata_files: dict[str, SemanticRecord] = {}
    pending_files: list[PendingSemanticFile] = []
    regular_contents: dict[str, FileContent] = {}
    hardlinks: dict[str, str] = {}
    ignored_files: Counter[str] = Counter()
    present_paths: set[str] = set()
    regular_like_paths: set[str] = set()
    top_levels: set[str] = set()
    declared_file_bytes = 0
    member_count = 0

    with tarfile.open(fileobj=stream, mode="r|") as archive:
        for member in archive:
            member_count += 1
            if member_count > max_members:
                raise ArchiveInspectionError(
                    f"archive has more than the allowed {max_members} members"
                )

            path = _normalize_member_name(member.name)
            if path in present_paths:
                raise ArchiveInspectionError(f"archive contains duplicate path: {path!r}")
            present_paths.add(path)
            top_levels.add(path.split("/", 1)[0])

            forbidden = _forbidden_state(path)
            if forbidden is not None:
                raise ArchiveInspectionError(
                    f"archive contains forbidden {forbidden}: {path}"
                )

            is_semantic, category = _classify_file(path)
            mode = member.mode & 0o7777

            if member.isdir():
                record = SemanticRecord(kind="directory", mode=mode)
                if is_semantic:
                    semantic_files[path] = record
                else:
                    metadata_files[path] = record
                    ignored_files[category] += 1
                continue

            if member.isfile():
                if member.size < 0 or member.size > max_member_bytes:
                    raise ArchiveInspectionError(
                        f"archive member {path!r} has disallowed size {member.size}"
                    )
                declared_file_bytes += member.size
                if declared_file_bytes > max_archive_bytes:
                    raise ArchiveInspectionError(
                        "archive's declared regular-file contents exceed "
                        f"the allowed {max_archive_bytes} bytes"
                    )

                # Hash every regular file so hard links can be resolved without
                # extraction.  Metadata records deliberately omit the hash.
                extracted = archive.extractfile(member)
                if extracted is None:
                    raise ArchiveInspectionError(f"cannot read regular member: {path}")
                canonical_trace = is_semantic and _is_lake_build_trace(path)
                with extracted:
                    regular_contents[path] = _hash_stream(
                        extracted,
                        member.size,
                        path,
                        canonicalize_trace=canonical_trace,
                    )

                regular_like_paths.add(path)
                if is_semantic:
                    pending_files.append(
                        PendingSemanticFile(path, path, mode, canonical_trace)
                    )
                else:
                    metadata_files[path] = SemanticRecord(kind="file", mode=mode)
                    ignored_files[category] += 1
                continue

            if member.islnk():
                target = _normalize_member_name(member.linkname)
                hardlinks[path] = target
                regular_like_paths.add(path)
                if is_semantic:
                    pending_files.append(
                        PendingSemanticFile(
                            path,
                            target,
                            mode,
                            _is_lake_build_trace(path),
                        )
                    )
                else:
                    metadata_files[path] = SemanticRecord(kind="file", mode=mode)
                    ignored_files[category] += 1
                continue

            if member.issym():
                target = _normalize_symlink_target(path, member.linkname)
                if is_semantic:
                    semantic_files[path] = SemanticRecord(
                        kind="symlink",
                        mode=mode,
                        sha256=hashlib.sha256(target.encode("utf-8")).hexdigest(),
                        size=0,
                        link_target=target,
                    )
                else:
                    metadata_files[path] = SemanticRecord(
                        kind="symlink", mode=mode, link_target=target
                    )
                    ignored_files[category] += 1
                continue

            raise ArchiveInspectionError(
                f"archive contains unsupported special member {path!r} "
                f"(tar type {member.type!r})"
            )

    # Validate every hard link, including content-ignored metadata links.
    for path in hardlinks:
        _resolve_content(path, regular_contents, hardlinks)

    for pending in pending_files:
        content = _resolve_content(pending.content_path, regular_contents, hardlinks)
        if pending.canonical_trace and not content.canonical_trace:
            raise ArchiveInspectionError(
                f"Lake trace hard link {pending.path!r} targets non-trace content"
            )
        semantic_files[pending.path] = SemanticRecord(
            kind="file",
            mode=pending.mode,
            sha256=content.sha256,
            size=content.size,
        )

    return ArchiveInventory(
        semantic_files=semantic_files,
        metadata_files=metadata_files,
        ignored_files=ignored_files,
        present_paths=present_paths,
        regular_like_paths=regular_like_paths,
        top_levels=top_levels,
        member_count=member_count,
        declared_file_bytes=declared_file_bytes,
    )


def _validate_layout(inventory: ArchiveInventory) -> None:
    if inventory.top_levels != EXPECTED_TOP_LEVELS:
        raise ArchiveInspectionError(
            "unexpected top-level archive entries: "
            f"expected {sorted(EXPECTED_TOP_LEVELS)}, got {sorted(inventory.top_levels)}"
        )

    missing = REQUIRED_MEMBER_PATHS - inventory.present_paths
    if missing:
        raise ArchiveInspectionError(
            "archive is missing required members: " + ", ".join(sorted(missing))
        )

    all_records = inventory.comparison_records()
    bad_required = {
        path
        for path in REQUIRED_MEMBER_PATHS
        if path not in inventory.regular_like_paths
        and (path not in all_records or all_records[path].kind != "symlink")
    }
    if bad_required:
        raise ArchiveInspectionError(
            "required members are not files or links: " + ", ".join(sorted(bad_required))
        )

    not_executable = {
        path
        for path in REQUIRED_EXECUTABLE_PATHS
        if all_records[path].mode & 0o111 == 0
    }
    if not_executable:
        raise ArchiveInspectionError(
            "required commands are not executable: "
            + ", ".join(sorted(not_executable))
        )

    build_outputs = {
        path for path in inventory.semantic_files if _is_lake_build_path(path)
    }
    required_kinds = {
        ".olean": any(path.endswith(".olean") for path in build_outputs),
        ".ilean": any(path.endswith(".ilean") for path in build_outputs),
        ".c": any(path.endswith(".c") for path in build_outputs),
        "Mathlib .olean": any(
            path.startswith("aeneas/packages/mathlib/.lake/build/")
            and path.endswith(".olean")
            for path in build_outputs
        ),
    }
    missing_kinds = [name for name, present in required_kinds.items() if not present]
    if missing_kinds:
        raise ArchiveInspectionError(
            "archive lacks expected Lean build output kinds: " + ", ".join(missing_kinds)
        )


def inspect_archive(
    path: Path,
    *,
    zstd: str = "zstd",
    max_members: int = DEFAULT_MAX_MEMBERS,
    max_member_bytes: int = DEFAULT_MAX_MEMBER_BYTES,
    max_archive_bytes: int = DEFAULT_MAX_ARCHIVE_BYTES,
    validate_layout: bool = True,
) -> ArchiveInventory:
    """Safely stream and inventory one ``.tar.zst`` toolchain archive."""

    requested_path = path
    try:
        # Nix output links are commonly symlinks.  Passing the resolved store
        # path also avoids zstd implementations that decline symlink inputs.
        path = path.resolve(strict=True)
    except OSError as error:
        raise ArchiveInspectionError(
            f"cannot resolve archive {requested_path}: {error}"
        ) from error
    if not path.is_file():
        raise ArchiveInspectionError(
            f"archive is not a regular file: {requested_path} (resolved to {path})"
        )
    try:
        with path.open("rb") as archive_file:
            if archive_file.read(len(ZSTD_MAGIC)) != ZSTD_MAGIC:
                raise ArchiveInspectionError(f"archive is not a standard zstd frame: {path}")
    except OSError as error:
        raise ArchiveInspectionError(f"cannot read archive {path}: {error}") from error

    stderr_file = tempfile.TemporaryFile()
    try:
        try:
            process = subprocess.Popen(
                [zstd, "--decompress", "--stdout", "--quiet", "--", os.fspath(path)],
                stdout=subprocess.PIPE,
                stderr=stderr_file,
            )
        except OSError as error:
            raise ArchiveInspectionError(f"cannot execute {zstd!r}: {error}") from error

        assert process.stdout is not None
        inventory: ArchiveInventory | None = None
        inspection_error: Exception | None = None
        try:
            inventory = _read_tar_stream(
                process.stdout,
                max_members=max_members,
                max_member_bytes=max_member_bytes,
                max_archive_bytes=max_archive_bytes,
            )
        except Exception as error:  # Preserve zstd diagnostics below.
            inspection_error = error
        finally:
            process.stdout.close()

        if inspection_error is not None and process.poll() is None:
            process.terminate()
        try:
            return_code = process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            process.kill()
            return_code = process.wait()

        stderr_file.seek(0)
        stderr = stderr_file.read().decode("utf-8", errors="replace").strip()
        if inspection_error is not None:
            detail = f"; zstd: {stderr}" if stderr else ""
            if isinstance(inspection_error, ArchiveInspectionError):
                raise ArchiveInspectionError(
                    f"{path}: {inspection_error}{detail}"
                ) from inspection_error
            raise ArchiveInspectionError(
                f"failed to read tar stream from {path}: {inspection_error}{detail}"
            ) from inspection_error
        if return_code != 0:
            raise ArchiveInspectionError(
                f"zstd failed for {path} with exit code {return_code}: {stderr}"
            )
        assert inventory is not None
    finally:
        stderr_file.close()

    if validate_layout:
        _validate_layout(inventory)
    return inventory


def compare_inventories(
    first: ArchiveInventory, second: ArchiveInventory
) -> ComparisonResult:
    first_records = first.comparison_records()
    second_records = second.comparison_records()
    first_paths = set(first_records)
    second_paths = set(second_records)
    common = first_paths & second_paths
    changed = tuple(
        sorted(path for path in common if first_records[path] != second_records[path])
    )
    return ComparisonResult(
        only_first=tuple(sorted(first_paths - second_paths)),
        only_second=tuple(sorted(second_paths - first_paths)),
        changed=changed,
    )


def _format_size(size: int) -> str:
    value = float(size)
    for suffix in ("B", "KiB", "MiB", "GiB", "TiB"):
        if value < 1024 or suffix == "TiB":
            return f"{value:.1f} {suffix}"
        value /= 1024
    raise AssertionError("unreachable")


def _print_inventory(label: str, path: Path, inventory: ArchiveInventory) -> None:
    semantic_bytes = sum(
        record.size for record in inventory.semantic_files.values() if record.kind == "file"
    )
    ignored = ", ".join(
        f"{category}={count}" for category, count in sorted(inventory.ignored_files.items())
    )
    print(
        f"{label}: {path}\n"
        f"  {len(inventory.semantic_files)} semantic entries "
        f"({_format_size(semantic_bytes)}), {inventory.member_count} archive members"
    )
    if ignored:
        print(f"  ignored metadata: {ignored}")


def _print_paths(heading: str, paths: Iterable[str], limit: int) -> None:
    paths = tuple(paths)
    if not paths:
        return
    print(f"{heading} ({len(paths)}):")
    for path in paths[:limit]:
        print(f"  {path}")
    if len(paths) > limit:
        print(f"  ... and {len(paths) - limit} more")


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("first_archive", type=Path, help="first actual .tar.zst archive")
    parser.add_argument("second_archive", type=Path, help="second actual .tar.zst archive")
    parser.add_argument(
        "--zstd", default="zstd", help="zstd executable to use (default: %(default)s)"
    )
    parser.add_argument(
        "--max-differences",
        type=int,
        default=50,
        help="maximum paths to print in each difference category (default: %(default)s)",
    )
    parser.add_argument(
        "--max-members", type=int, default=DEFAULT_MAX_MEMBERS, help=argparse.SUPPRESS
    )
    parser.add_argument(
        "--max-member-bytes",
        type=int,
        default=DEFAULT_MAX_MEMBER_BYTES,
        help=argparse.SUPPRESS,
    )
    parser.add_argument(
        "--max-archive-bytes",
        type=int,
        default=DEFAULT_MAX_ARCHIVE_BYTES,
        help=argparse.SUPPRESS,
    )
    args = parser.parse_args(argv)
    for name in (
        "max_differences",
        "max_members",
        "max_member_bytes",
        "max_archive_bytes",
    ):
        if getattr(args, name) <= 0:
            parser.error(f"--{name.replace('_', '-')} must be positive")
    return args


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    inspect_kwargs = {
        "zstd": args.zstd,
        "max_members": args.max_members,
        "max_member_bytes": args.max_member_bytes,
        "max_archive_bytes": args.max_archive_bytes,
    }
    try:
        first = inspect_archive(args.first_archive, **inspect_kwargs)
        second = inspect_archive(args.second_archive, **inspect_kwargs)
    except ArchiveInspectionError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 2

    _print_inventory("first", args.first_archive, first)
    _print_inventory("second", args.second_archive, second)
    result = compare_inventories(first, second)
    if result.equivalent:
        print("Archives are semantically equivalent.")
        return 0

    print("Archives are NOT semantically equivalent.", file=sys.stderr)
    _print_paths("Only in first archive", result.only_first, args.max_differences)
    _print_paths("Only in second archive", result.only_second, args.max_differences)
    if result.changed:
        print(f"Different content, type, or mode ({len(result.changed)}):")
        first_records = first.comparison_records()
        second_records = second.comparison_records()
        for path in result.changed[: args.max_differences]:
            print(f"  {path}")
            print(f"    first:  {first_records[path].short_description()}")
            print(f"    second: {second_records[path].short_description()}")
        if len(result.changed) > args.max_differences:
            print(f"  ... and {len(result.changed) - args.max_differences} more")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
