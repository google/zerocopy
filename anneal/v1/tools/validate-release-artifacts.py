#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Validate untrusted Anneal release metadata and, optionally, archives.

This helper is intended to run from a trusted workflow checkout. Metadata and
archives produced by release matrix jobs are untrusted inputs: do not move this
validation into the checkout used to build those inputs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
import tomllib
from pathlib import Path


# Keep this in sync with the release matrix in
# .github/workflows/anneal-release.yml and the exocrate sections in
# anneal/v1/Cargo.toml. Exact validation is deliberate: adding or renaming a
# release platform must fail until every consumer of the platform matrix has
# been reviewed and updated together.
EXPECTED_TARGETS = {
    "linux-x86_64": ("linux", "x86_64"),
    "linux-aarch64": ("linux", "aarch64"),
    "macos-x86_64": ("macos", "x86_64"),
    "macos-aarch64": ("macos", "aarch64"),
}

# collect-release-archive-metadata.py is the producer of this schema. Keep the
# two helpers coordinated; accepting unknown keys would let a producer change
# meaning without requiring a corresponding change to this trusted validator.
EXPECTED_METADATA_KEYS = frozenset(
    {"target", "os", "arch", "filename", "sha256", "url"}
)

# GitHub documents a maximum size of 2 GiB minus one byte for a single release
# asset. Check the actual file, rather than trusting matrix-produced metadata.
GITHUB_RELEASE_ASSET_SIZE_LIMIT = 2_147_483_647
MAX_METADATA_FILE_SIZE = 64 * 1024
MAX_CARGO_TOML_SIZE = 1024 * 1024
SHA256_RE = re.compile(r"[0-9a-f]{64}")


class ValidationError(Exception):
    """An untrusted release artifact did not match the trusted contract."""


def archive_filename(target: str) -> str:
    return f"anneal-toolchain-{target}.tar.zst"


def release_url(repository: str, tag: str, filename: str) -> str:
    return f"https://github.com/{repository}/releases/download/{tag}/{filename}"


def _require_directory(path: Path, description: str) -> None:
    try:
        mode = path.lstat().st_mode
    except OSError as error:
        raise ValidationError(f"cannot inspect {description} {path}: {error}") from error
    if not stat.S_ISDIR(mode):
        raise ValidationError(f"{description} is not a non-symlink directory: {path}")


def _require_regular_file(path: Path, description: str) -> os.stat_result:
    try:
        file_stat = path.lstat()
    except OSError as error:
        raise ValidationError(f"cannot inspect {description} {path}: {error}") from error
    if not stat.S_ISREG(file_stat.st_mode):
        raise ValidationError(f"{description} is not a regular non-symlink file: {path}")
    return file_stat


def _require_exact_directory_entries(
    directory: Path, expected_names: set[str], description: str
) -> dict[str, Path]:
    _require_directory(directory, f"{description} directory")
    try:
        entries = {entry.name: entry for entry in directory.iterdir()}
    except OSError as error:
        raise ValidationError(
            f"cannot list {description} directory {directory}: {error}"
        ) from error

    actual_names = set(entries)
    missing = sorted(expected_names - actual_names)
    unexpected = sorted(actual_names - expected_names)
    errors = []
    if missing:
        errors.append("missing " + ", ".join(missing))
    if unexpected:
        errors.append("unexpected " + ", ".join(unexpected))
    if errors:
        raise ValidationError(f"invalid {description} directory {directory}: {'; '.join(errors)}")
    return entries


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValidationError(f"duplicate JSON key {key!r}")
        value[key] = item
    return value


def _reject_json_constant(value: str):
    raise ValidationError(f"invalid JSON constant {value!r}")


def _load_json(path: Path) -> object:
    file_stat = _require_regular_file(path, "metadata file")
    if file_stat.st_size > MAX_METADATA_FILE_SIZE:
        raise ValidationError(
            f"metadata file {path} is {file_stat.st_size} bytes; "
            f"maximum is {MAX_METADATA_FILE_SIZE} bytes"
        )
    try:
        contents = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise ValidationError(f"cannot read metadata file {path}: {error}") from error
    try:
        return json.loads(
            contents,
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_json_constant,
        )
    except (json.JSONDecodeError, ValidationError) as error:
        raise ValidationError(f"invalid metadata file {path}: {error}") from error


def _validate_metadata(
    path: Path, target: str, platform: tuple[str, str], tag: str, repository: str
) -> dict[str, str]:
    value = _load_json(path)
    if not isinstance(value, dict):
        raise ValidationError(f"metadata file {path} must contain one JSON object")

    actual_keys = set(value)
    missing = sorted(EXPECTED_METADATA_KEYS - actual_keys)
    unexpected = sorted(actual_keys - EXPECTED_METADATA_KEYS)
    if missing or unexpected:
        details = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if unexpected:
            details.append("unexpected " + ", ".join(unexpected))
        raise ValidationError(f"metadata file {path} has invalid keys: {'; '.join(details)}")

    non_strings = sorted(key for key, item in value.items() if not isinstance(item, str))
    if non_strings:
        raise ValidationError(
            f"metadata file {path} has non-string values for: {', '.join(non_strings)}"
        )

    # The exact key and type checks above establish this narrower runtime type.
    metadata: dict[str, str] = value
    os_name, arch = platform
    filename = archive_filename(target)
    expected_fields = {
        "target": target,
        "os": os_name,
        "arch": arch,
        "filename": filename,
        "url": release_url(repository, tag, filename),
    }
    for key, expected in expected_fields.items():
        if metadata[key] != expected:
            raise ValidationError(
                f"metadata file {path} has {key}={metadata[key]!r}; expected {expected!r}"
            )

    if SHA256_RE.fullmatch(metadata["sha256"]) is None:
        raise ValidationError(
            f"metadata file {path} sha256 must be 64 lowercase hexadecimal characters"
        )
    return metadata


def _sha256_file(path: Path) -> str:
    hasher = hashlib.sha256()
    try:
        with path.open("rb") as archive:
            for chunk in iter(lambda: archive.read(1024 * 1024), b""):
                hasher.update(chunk)
    except OSError as error:
        raise ValidationError(f"cannot read archive file {path}: {error}") from error
    return hasher.hexdigest()


def _validate_archive(path: Path, expected_sha256: str) -> None:
    file_stat = _require_regular_file(path, "archive file")
    if file_stat.st_size > GITHUB_RELEASE_ASSET_SIZE_LIMIT:
        raise ValidationError(
            f"archive file {path} is {file_stat.st_size} bytes; GitHub release assets "
            f"must not exceed {GITHUB_RELEASE_ASSET_SIZE_LIMIT} bytes"
        )

    actual_sha256 = _sha256_file(path)
    if actual_sha256 != expected_sha256:
        raise ValidationError(
            f"archive file {path} has sha256 {actual_sha256}; expected {expected_sha256}"
        )


def _load_cargo_toml(path: Path) -> dict[str, object]:
    file_stat = _require_regular_file(path, "Cargo manifest")
    if file_stat.st_size > MAX_CARGO_TOML_SIZE:
        raise ValidationError(
            f"Cargo manifest {path} is {file_stat.st_size} bytes; "
            f"maximum is {MAX_CARGO_TOML_SIZE} bytes"
        )
    try:
        contents = path.read_text(encoding="utf-8")
        value = tomllib.loads(contents)
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        raise ValidationError(f"invalid Cargo manifest {path}: {error}") from error
    return value


def _require_table(value: object, path: str, manifest: Path) -> dict[str, object]:
    if not isinstance(value, dict):
        raise ValidationError(
            f"Cargo manifest {manifest} {path} must be a table"
        )
    return value


def validate_cargo_exocrate_metadata(
    cargo_toml: Path, metadata: dict[str, dict[str, str]]
) -> None:
    """Bind cargo-anneal's embedded archive metadata to validated artifacts."""

    manifest = _load_cargo_toml(cargo_toml)
    package = _require_table(manifest.get("package"), "package", cargo_toml)
    package_metadata = _require_table(
        package.get("metadata"), "package.metadata", cargo_toml
    )
    exocrate = _require_table(
        package_metadata.get("exocrate"),
        "package.metadata.exocrate",
        cargo_toml,
    )

    expected_by_platform = {
        (os_name, arch): {
            "sha256": metadata[target]["sha256"],
            "url": metadata[target]["url"],
        }
        for target, (os_name, arch) in EXPECTED_TARGETS.items()
    }
    expected_os_names = {os_name for os_name, _ in expected_by_platform}
    actual_os_names = set(exocrate)
    if actual_os_names != expected_os_names:
        raise ValidationError(
            f"Cargo manifest {cargo_toml} package.metadata.exocrate has "
            f"platforms {sorted(actual_os_names)}; expected "
            f"{sorted(expected_os_names)}"
        )

    for os_name in sorted(expected_os_names):
        by_arch = _require_table(
            exocrate[os_name],
            f"package.metadata.exocrate.{os_name}",
            cargo_toml,
        )
        expected_arches = {
            arch
            for platform_os, arch in expected_by_platform
            if platform_os == os_name
        }
        actual_arches = set(by_arch)
        if actual_arches != expected_arches:
            raise ValidationError(
                f"Cargo manifest {cargo_toml} "
                f"package.metadata.exocrate.{os_name} has architectures "
                f"{sorted(actual_arches)}; expected {sorted(expected_arches)}"
            )

        for arch in sorted(expected_arches):
            path = f"package.metadata.exocrate.{os_name}.{arch}"
            values = _require_table(by_arch[arch], path, cargo_toml)
            expected_values = expected_by_platform[(os_name, arch)]
            if set(values) != set(expected_values):
                raise ValidationError(
                    f"Cargo manifest {cargo_toml} {path} has keys "
                    f"{sorted(values)}; expected {sorted(expected_values)}"
                )
            for key, expected in expected_values.items():
                actual = values[key]
                if not isinstance(actual, str) or actual != expected:
                    raise ValidationError(
                        f"Cargo manifest {cargo_toml} {path}.{key} is "
                        f"{actual!r}; expected {expected!r}"
                    )


def validate_release_artifacts(
    metadata_dir: Path,
    tag: str,
    repository: str,
    archive_dir: Path | None = None,
) -> dict[str, dict[str, str]]:
    """Validate and return metadata indexed by its exact release target."""

    expected_metadata_names = {f"{target}.json" for target in EXPECTED_TARGETS}
    metadata_entries = _require_exact_directory_entries(
        metadata_dir, expected_metadata_names, "metadata"
    )

    metadata = {
        target: _validate_metadata(
            metadata_entries[f"{target}.json"], target, platform, tag, repository
        )
        for target, platform in EXPECTED_TARGETS.items()
    }

    if archive_dir is not None:
        expected_archive_names = {archive_filename(target) for target in EXPECTED_TARGETS}
        archive_entries = _require_exact_directory_entries(
            archive_dir, expected_archive_names, "archive"
        )
        for target in EXPECTED_TARGETS:
            filename = archive_filename(target)
            _validate_archive(archive_entries[filename], metadata[target]["sha256"])

    return metadata


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--metadata-dir", required=True, type=Path)
    parser.add_argument("--archive-dir", type=Path)
    parser.add_argument("--cargo-toml", type=Path)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--repository", required=True)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        metadata = validate_release_artifacts(
            metadata_dir=args.metadata_dir,
            archive_dir=args.archive_dir,
            tag=args.tag,
            repository=args.repository,
        )
        if args.cargo_toml is not None:
            validate_cargo_exocrate_metadata(args.cargo_toml, metadata)
    except ValidationError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
