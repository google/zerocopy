# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Corpus tree hashing and manifests, Miri test headers, and compile flags."""

from __future__ import annotations

import errno
import hashlib
import hmac
import os
from pathlib import Path
import stat

from .common import (
    DOWNLOAD_CHUNK_BYTES, MAX_CORPUS_DIR_DEPTH, MAX_CORPUS_DIR_ENTRIES, MAX_SINGLE_FILE_BYTES,
    MAX_TOTAL_EXTRACTED_BYTES, MIRI_HEADER_RE, OracleError,
)


def _stream_regular_file_sha256(
    path: str | Path,
    *,
    max_bytes: int,
    copy_to: Path | None = None,
    dir_fd: int | None = None,
    display_path: Path | None = None,
) -> tuple[str, int]:
    """Hash a regular, non-symlink file with bounded streaming I/O.

    Opens with `O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC` (anchored at `dir_fd`
    when provided so concurrent ancestor/entry renames cannot redirect the
    open), then verifies `S_ISREG` and `st_size` on the opened file descriptor
    before streaming chunks up to `max_bytes`. When `copy_to` is provided,
    writes the exact verified bytes to `copy_to` in the same read pass so
    callers never reopen the source path after hashing.
    """
    shown = display_path if display_path is not None else path
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    if hasattr(os, "O_NONBLOCK"):
        flags |= os.O_NONBLOCK
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        if dir_fd is not None:
            fd = os.open(path, flags, dir_fd=dir_fd)
        else:
            fd = os.open(path, flags)
    except OSError as exc:
        raise OracleError(f"failed to open corpus file '{shown}': {exc}") from exc
    out_fh = None
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise OracleError(f"corpus contains non-regular file: {shown}")
        if st.st_size > max_bytes:
            raise OracleError(
                f"corpus file exceeds size limit ({st.st_size} > {max_bytes}): {shown}"
            )
        if copy_to is not None:
            copy_to.parent.mkdir(parents=True, exist_ok=True)
            out_fh = copy_to.open("xb")
        hasher = hashlib.sha256()
        total = 0
        with os.fdopen(fd, "rb", closefd=False) as fh:
            while True:
                chunk = fh.read(DOWNLOAD_CHUNK_BYTES)
                if not chunk:
                    break
                total += len(chunk)
                if total > max_bytes:
                    raise OracleError(
                        f"corpus file exceeded size limit during read: {shown}"
                    )
                hasher.update(chunk)
                if out_fh is not None:
                    out_fh.write(chunk)
        return hasher.hexdigest(), total
    except BaseException:
        if out_fh is not None:
            out_fh.close()
            out_fh = None
        if copy_to is not None:
            copy_to.unlink(missing_ok=True)
        raise
    finally:
        if out_fh is not None:
            out_fh.close()
        os.close(fd)


def _walk_corpus_tree(
    corpus_dir: Path,
    subdirs: list[str],
    *,
    suffixes: tuple[str, ...],
    max_entries: int = MAX_CORPUS_DIR_ENTRIES,
    max_depth: int = MAX_CORPUS_DIR_DEPTH,
    max_matching_files: int | None = None,
    snapshot_dir: Path | None = None,
    label: str = "corpus",
) -> tuple[str, list[str]]:
    """Bounded streaming directory walk computing a canonical SHA-256 manifest.

    Anchors every directory descent and file open to open parent directory
    descriptors (`dir_fd` with `O_NOFOLLOW | O_DIRECTORY | O_CLOEXEC`) and
    `os.scandir`, rejecting symlinks, non-regular files (such as FIFOs),
    excessive entry counts or nesting depth, and byte-limit overflows. When
    `snapshot_dir` is given, copies every matched file into `snapshot_dir`
    during the single hashing pass so later processing never reopens
    `corpus_dir`.
    """
    if corpus_dir.is_symlink():
        raise OracleError(f"{label} directory must not be a symlink: {corpus_dir}")
    root = corpus_dir.resolve()
    snap_root = snapshot_dir.resolve() if snapshot_dir is not None else None
    if snap_root is not None:
        snap_root.mkdir(parents=True, exist_ok=True)
    entries: list[tuple[str, str]] = []
    total_bytes = 0
    seen_entries = 0
    dir_flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0)
    )
    try:
        root_fd = os.open(corpus_dir, dir_flags)
    except OSError as exc:
        if exc.errno == errno.ELOOP:
            raise OracleError(
                f"{label} directory must not be a symlink: {corpus_dir}"
            ) from exc
        raise OracleError(
            f"failed opening {label} directory '{corpus_dir}': {exc}"
        ) from exc

    try:
        for sub in subdirs:
            rel_sub = sub[len("tests/"):] if sub.startswith("tests/") else sub
            cur_path = root
            cur_fd = os.open(".", dir_flags, dir_fd=root_fd)
            try:
                if rel_sub:
                    for part in Path(rel_sub).parts:
                        if part in ("", "."):
                            continue
                        if part == ".." or "/" in part or "\\" in part:
                            raise OracleError(
                                f"unsafe {label} subdirectory component: {rel_sub}"
                            )
                        cur_path = cur_path / part
                        try:
                            next_fd = os.open(part, dir_flags, dir_fd=cur_fd)
                        except OSError as exc:
                            if exc.errno == errno.ELOOP:
                                raise OracleError(
                                    f"{label} directory must not be a symlink: "
                                    f"{cur_path}"
                                ) from exc
                            if exc.errno in (errno.ENOENT, errno.ENOTDIR):
                                raise OracleError(
                                    f"missing {label} subdirectory: {cur_path}"
                                ) from exc
                            raise OracleError(
                                f"failed opening {label} directory "
                                f"'{cur_path}': {exc}"
                            ) from exc
                        os.close(cur_fd)
                        cur_fd = next_fd
            except BaseException:
                os.close(cur_fd)
                raise

            stack: list[tuple[int, Path, int]] = [(cur_fd, cur_path, 0)]
            try:
                while stack:
                    dir_fd, cur_dir, depth = stack.pop()
                    try:
                        if depth > max_depth:
                            raise OracleError(
                                f"{label} directory exceeds max depth "
                                f"({max_depth}): {cur_dir}"
                            )
                        with os.scandir(dir_fd) as it:
                            for entry in it:
                                seen_entries += 1
                                if seen_entries > max_entries:
                                    raise OracleError(
                                        f"{label} directory exceeds max entry "
                                        f"limit ({max_entries})"
                                    )
                                epath = cur_dir / entry.name
                                if entry.is_symlink():
                                    raise OracleError(
                                        f"{label} contains forbidden symlink: "
                                        f"{epath}"
                                    )
                                if entry.is_dir(follow_symlinks=False):
                                    if depth + 1 > max_depth:
                                        raise OracleError(
                                            f"{label} directory exceeds max "
                                            f"depth ({max_depth}): {epath}"
                                        )
                                    try:
                                        child_fd = os.open(
                                            entry.name,
                                            dir_flags,
                                            dir_fd=dir_fd,
                                        )
                                    except OSError as exc:
                                        if exc.errno == errno.ELOOP:
                                            raise OracleError(
                                                f"{label} contains forbidden "
                                                f"symlink dir: {epath}"
                                            ) from exc
                                        raise OracleError(
                                            f"failed opening {label} directory "
                                            f"'{epath}': {exc}"
                                        ) from exc
                                    stack.append((child_fd, epath, depth + 1))
                                    continue
                                if not entry.name.endswith(suffixes):
                                    continue
                                if (
                                    max_matching_files is not None
                                    and len(entries) >= max_matching_files
                                ):
                                    raise OracleError(
                                        f"{label} file count mismatch: exceeds "
                                        f"expected {max_matching_files} files"
                                    )
                                rel = epath.relative_to(root).as_posix()
                                copy_dst = None
                                if snap_root is not None:
                                    copy_dst = (snap_root / rel).resolve()
                                    try:
                                        copy_dst.relative_to(snap_root)
                                    except ValueError as exc:
                                        raise OracleError(
                                            f"snapshot path escapes root: "
                                            f"{copy_dst}"
                                        ) from exc
                                digest, size = _stream_regular_file_sha256(
                                    entry.name,
                                    max_bytes=MAX_SINGLE_FILE_BYTES,
                                    copy_to=copy_dst,
                                    dir_fd=dir_fd,
                                    display_path=epath,
                                )
                                total_bytes += size
                                if total_bytes > MAX_TOTAL_EXTRACTED_BYTES:
                                    raise OracleError(
                                        f"{label} exceeds total size limit "
                                        f"({total_bytes} > "
                                        f"{MAX_TOTAL_EXTRACTED_BYTES})"
                                    )
                                entries.append((rel, digest))
                    finally:
                        os.close(dir_fd)
            finally:
                while stack:
                    rem_fd, _, _ = stack.pop()
                    os.close(rem_fd)
    finally:
        os.close(root_fd)

    entries.sort()
    manifest_text = "".join(f"{digest}  {rel}\n" for rel, digest in entries)
    manifest_sha = hashlib.sha256(manifest_text.encode("utf-8")).hexdigest()
    return manifest_sha, [rel for rel, _ in entries]


def compute_corpus_manifest_sha256(
    corpus_dir: Path,
    extract_subdirs: list[str],
    *,
    max_entries: int = MAX_CORPUS_DIR_ENTRIES,
    max_rs_files: int | None = None,
    snapshot_dir: Path | None = None,
) -> tuple[str, list[str]]:
    """Compute canonical SHA-256 over sorted `<sha256>  <relpath>\\n` `.rs`."""
    return _walk_corpus_tree(
        corpus_dir,
        extract_subdirs,
        suffixes=(".rs",),
        max_entries=max_entries,
        max_depth=MAX_CORPUS_DIR_DEPTH,
        max_matching_files=max_rs_files,
        snapshot_dir=snapshot_dir,
        label="corpus",
    )


def verify_corpus_manifest(
    corpus_dir: Path,
    pin: dict[str, object],
    *,
    snapshot_dir: Path | None = None,
) -> tuple[str, list[str]]:
    """Fail-closed check of extracted/local corpus file count and digest."""
    subdirs = list(pin["extract_subdirs"])  # type: ignore[arg-type]
    expected_count = int(pin["expected_file_count"])  # type: ignore[arg-type]
    actual_sha, files = compute_corpus_manifest_sha256(
        corpus_dir,
        subdirs,
        max_rs_files=expected_count,
        snapshot_dir=snapshot_dir,
    )
    if len(files) != expected_count:
        raise OracleError(
            f"corpus file count mismatch: expected {expected_count}, "
            f"found {len(files)}"
        )
    expected_sha = str(pin["corpus_manifest_sha256"])
    if not hmac.compare_digest(actual_sha, expected_sha):
        raise OracleError(
            f"corpus manifest SHA-256 mismatch: "
            f"expected {expected_sha}, got {actual_sha}"
        )
    return actual_sha, files


def parse_miri_headers(text: str) -> dict[str, object]:
    """Parse relevant `//@` ui_test directives from upstream Miri fail tests.

    Target and bitwidth filters (`only-target`, `ignore-target`,
    `ignore-bitwidth`) are keyed by optional `[rev]` qualifier just like
    `compile-flags`, and multiple `//@revisions:` lines accumulate rather
    than overwriting earlier declarations.
    """
    revisions: list[str] = []
    flags: dict[str | None, list[str]] = {None: []}
    only_targets: dict[str | None, list[list[str]]] = {None: []}
    ignore_targets: dict[str | None, list[list[str]]] = {None: []}
    ignore_bitwidth: dict[str | None, list[str]] = {None: []}

    for line in text.splitlines():
        match = MIRI_HEADER_RE.match(line.strip())
        if not match:
            continue
        rev, key, raw_val = match.group(1), match.group(2), match.group(3)
        val = raw_val.split("#", 1)[0].strip()
        if key == "revisions":
            for r in val.split():
                if r not in revisions:
                    revisions.append(r)
        elif key == "compile-flags":
            flags.setdefault(rev, []).extend(val.split())
        elif key == "only-target":
            only_targets.setdefault(rev, []).append(val.split())
        elif key == "ignore-target":
            ignore_targets.setdefault(rev, []).append(val.split())
        elif key == "ignore-bitwidth":
            ignore_bitwidth.setdefault(rev, []).extend(val.split())

    return {
        "revisions": revisions,
        "flags": flags,
        "only_targets": only_targets,
        "ignore_targets": ignore_targets,
        "ignore_bitwidth": ignore_bitwidth,
    }


def _target_bitwidth(target: str) -> str:
    """Return pointer width (`'32'` or `'64'`) inferred from a Rust target triple."""
    arch = target.split("-", 1)[0]
    if arch in {"i386", "i586", "i686", "wasm32", "riscv32", "arm", "armv7", "mips", "powerpc"} or arch.startswith(
        ("thumbv", "armv", "riscv32")
    ):
        return "32"
    return "64"


def harness_skip_reason(
    hdr: dict[str, object], target: str, revision: str | None = None
) -> str | None:
    """Return a target-mismatch skip reason for `target` and `revision`."""
    only_map: dict[str | None, list[list[str]]] = hdr["only_targets"]  # type: ignore[assignment]
    ignore_map: dict[str | None, list[list[str]]] = hdr["ignore_targets"]  # type: ignore[assignment]
    bitwidth_map: dict[str | None, list[str]] = hdr["ignore_bitwidth"]  # type: ignore[assignment]

    only_list = list(only_map.get(None, []))
    ignore_list = list(ignore_map.get(None, []))
    bitwidth_list = list(bitwidth_map.get(None, []))
    if revision is not None:
        only_list.extend(only_map.get(revision, []))
        ignore_list.extend(ignore_map.get(revision, []))
        bitwidth_list.extend(bitwidth_map.get(revision, []))

    for pats in only_list:
        if not any(p in target for p in pats):
            return f"only-target {' '.join(pats)}"
    for pats in ignore_list:
        if any(p in target for p in pats):
            return f"ignore-target {' '.join(pats)}"
    bw = _target_bitwidth(target)
    if bw in bitwidth_list:
        return f"ignore-bitwidth {bw}"
    return None


# Baseline rustc flags unconditionally enforced by `anneal-rustc-capture`
# (`anneal/trusted/rustc-capture/src/capture.rs`). A Miri fixture that requests
# one of these flags already runs under the exact requested setting.
_CAPTURE_FIXED_RUSTC_FLAGS: frozenset[str] = frozenset({
    "-Copt-level=0",
    "-Cdebug-assertions=no",
    "-Cdebug-assertions=off",
    "-Cdebug-assertions=false",
    "-Coverflow-checks=no",
    "-Coverflow-checks=off",
    "-Coverflow-checks=false",
    "-Zmir-opt-level=0",
})


def parse_compile_flags(flags: list[str]) -> tuple[str, str, list[str]]:
    """Extract edition and panic strategy; record unforwarded rustc flags."""
    edition = "2021"
    panic = "unwind"
    unforwarded: list[str] = []
    i = 0
    while i < len(flags):
        flag = flags[i]
        if flag.startswith("--edition"):
            if "=" in flag:
                edition = flag.split("=", 1)[1]
                i += 1
            elif i + 1 < len(flags):
                edition = flags[i + 1]
                i += 2
            else:
                unforwarded.append(flag)
                i += 1
            continue
        if flag in ("-C", "-Z") and i + 1 < len(flags):
            flag = flag + flags[i + 1]
            i += 1
        if flag == "-Cpanic=abort":
            panic = "abort"
        elif flag == "-Cpanic=unwind":
            panic = "unwind"
        elif flag in _CAPTURE_FIXED_RUSTC_FLAGS:
            pass
        elif not flag.startswith("-Zmiri-"):
            unforwarded.append(flag)
        i += 1
    if edition not in ("2015", "2018", "2021", "2024"):
        unforwarded.append(f"--edition={edition}")
        edition = "2021"
    return edition, panic, unforwarded
