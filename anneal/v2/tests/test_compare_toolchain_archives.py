#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://opensource.org/licenses/Apache-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Focused tests for compare-toolchain-archives.py."""

from __future__ import annotations

import importlib.util
import io
import json
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "compare-toolchain-archives.py"
SPEC = importlib.util.spec_from_file_location("compare_toolchain_archives", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
compare_toolchain_archives = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = compare_toolchain_archives
SPEC.loader.exec_module(compare_toolchain_archives)


FileEntry = tuple[str, bytes, int]
HardLinkEntry = tuple[str, str, int]


def ilean_bytes(
    *,
    usages: list[list[object]] | None = None,
    decls: dict[str, object] | None = None,
    reference_key: str = "ref-key",
    definition: object = None,
) -> bytes:
    document = {
        "decls": {"Aeneas.test": [1, 2, 3, 4]} if decls is None else decls,
        "directImports": [["Init", False, False, False]],
        "module": "Aeneas",
        "references": {
            reference_key: {
                "definition": definition,
                "usages": [[1, 2, 3, 4, "Aeneas.test"]]
                if usages is None
                else usages,
            }
        },
        "version": 5,
    }
    return json.dumps(document, separators=(",", ":"), sort_keys=True).encode()


def trace_bytes(
    *,
    dep_hash: str = "0123456789abcdef",
    output_hash: str = "fedcba9876543210",
    context: str = "context",
) -> bytes:
    document = {
        "schemaVersion": "2025-09-10",
        "depHash": dep_hash,
        "outputs": {"i": f"{output_hash}.ilean"},
        "inputs": [[context, "1111111111111111"]],
        "log": [{"level": "trace", "message": context}],
        "synthetic": False,
    }
    return json.dumps(document, separators=(",", ":"), sort_keys=True).encode()


def minimal_entries() -> list[FileEntry | HardLinkEntry]:
    return [
        ("aeneas/bin/aeneas", b"aeneas-bin", 0o755),
        ("aeneas/bin/charon", b"charon-bin", 0o755),
        ("aeneas/bin/charon-driver", b"charon-driver-bin", 0o755),
        (
            "aeneas/backends/lean/.lake/config/aeneas/lakefile.olean",
            b"aeneas-config",
            0o444,
        ),
        (
            "aeneas/packages/mathlib/.lake/config/mathlib/lakefile.olean",
            b"mathlib-config",
            0o444,
        ),
        ("aeneas/packages/mathlib/lake-manifest.json", b"{}\n", 0o444),
        ("aeneas/backends/lean/lakefile.lean", b"import Lake\n", 0o444),
        (
            "aeneas/backends/lean/.lake/build/lib/lean/Aeneas.olean",
            b"aeneas-olean",
            0o444,
        ),
        (
            "aeneas/backends/lean/.lake/build/lib/lean/Aeneas.ilean",
            ilean_bytes(),
            0o444,
        ),
        (
            "aeneas/backends/lean/.lake/build/ir/Aeneas.c",
            b"/* generated C */\n",
            0o444,
        ),
        (
            "aeneas/packages/mathlib/.lake/build/lib/lean/Mathlib/Init.olean",
            b"mathlib-olean",
            0o444,
        ),
        ("lean/bin/lake", b"lake-bin", 0o755),
        ("lean/bin/lean", b"lean-bin", 0o755),
        ("lean/lib/lean/Init.olean", b"lean-library", 0o444),
        ("rust/bin/cargo", b"cargo-bin", 0o755),
        ("rust/bin/rustc", b"rustc-bin", 0o755),
        ("rust/lib/rustlib/components", b"rustc\ncargo\n", 0o444),
    ]


def replace_file(
    entries: list[FileEntry | HardLinkEntry], path: str, data: bytes, mode: int
) -> None:
    for index, entry in enumerate(entries):
        if entry[0] == path:
            entries[index] = (path, data, mode)
            return
    raise AssertionError(f"missing fixture entry: {path}")


def make_archive(
    directory: Path,
    name: str,
    entries: list[FileEntry | HardLinkEntry],
    *,
    compression_level: int = 1,
    mtime: int = 0,
) -> Path:
    tar_path = directory / f"{name}.tar"
    with tarfile.open(tar_path, "w", format=tarfile.PAX_FORMAT) as archive:
        for entry in entries:
            path = entry[0]
            info = tarfile.TarInfo(path)
            info.mtime = mtime
            info.uid = 123
            info.gid = 456
            if isinstance(entry[1], bytes):
                _, data, mode = entry
                info.size = len(data)
                info.mode = mode
                archive.addfile(info, io.BytesIO(data))
            else:
                _, target, mode = entry
                info.type = tarfile.LNKTYPE
                info.linkname = target
                info.mode = mode
                archive.addfile(info)

    archive_path = directory / f"{name}.tar.zst"
    with archive_path.open("wb") as output:
        subprocess.run(
            ["zstd", "--quiet", f"-{compression_level}", "--stdout", "--", tar_path],
            check=True,
            stdout=output,
        )
    return archive_path


@unittest.skipUnless(shutil.which("zstd"), "zstd is required for archive tests")
class CompareToolchainArchivesTests(unittest.TestCase):
    def inspect(self, archive: Path):
        return compare_toolchain_archives.inspect_archive(archive)

    def test_ignores_only_contextual_metadata_content_differences(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            first_entries = minimal_entries()
            second_entries = minimal_entries()
            trace = "aeneas/backends/lean/.lake/build/lib/lean/Aeneas.trace"
            first_entries.append((trace, trace_bytes(context="first context"), 0o444))
            second_entries.append((trace, trace_bytes(context="second context"), 0o444))
            metadata = [
                "aeneas/backends/lean/.lake/build/ir/Aeneas.setup.json",
                "aeneas/backends/lean/.lake/build/ir/Aeneas.rsp",
            ]
            for path in metadata:
                first_entries.append((path, b"first context", 0o444))
                second_entries.append((path, b"second context", 0o444))
            replace_file(
                second_entries,
                "aeneas/backends/lean/.lake/config/aeneas/lakefile.olean",
                b"different context-dependent config",
                0o444,
            )

            first = make_archive(directory, "first", first_entries, compression_level=1, mtime=1)
            second = make_archive(
                directory, "second", second_entries, compression_level=9, mtime=999
            )

            result = compare_toolchain_archives.compare_inventories(
                self.inspect(first), self.inspect(second)
            )
            self.assertTrue(result.equivalent)

    def test_ilean_usages_are_semantic(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            first_entries = minimal_entries()
            second_entries = minimal_entries()
            path = "aeneas/backends/lean/.lake/build/lib/lean/Aeneas.ilean"
            replace_file(
                first_entries,
                path,
                ilean_bytes(usages=[[1, 2, 3, 4, "Aeneas.test"]]),
                0o444,
            )
            replace_file(
                second_entries,
                path,
                ilean_bytes(usages=[[99, 98, 97, 96, "Aeneas.test"]]),
                0o444,
            )

            result = compare_toolchain_archives.compare_inventories(
                self.inspect(make_archive(directory, "first", first_entries)),
                self.inspect(make_archive(directory, "second", second_entries)),
            )
            self.assertEqual(result.changed, (path,))

    def test_ilean_declarations_reference_keys_and_definitions_are_semantic(self) -> None:
        variants = {
            "declaration": ilean_bytes(decls={"Aeneas.changed": [1, 2, 3, 4]}),
            "reference key": ilean_bytes(reference_key="different-reference"),
            "definition": ilean_bytes(definition=[5, 6, 7, 8]),
        }
        for index, (label, changed_ilean) in enumerate(variants.items()):
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                directory = Path(tmp)
                first_entries = minimal_entries()
                second_entries = minimal_entries()
                path = "aeneas/backends/lean/.lake/build/lib/lean/Aeneas.ilean"
                replace_file(second_entries, path, changed_ilean, 0o444)
                result = compare_toolchain_archives.compare_inventories(
                    self.inspect(make_archive(directory, f"first-{index}", first_entries)),
                    self.inspect(make_archive(directory, f"second-{index}", second_entries)),
                )
                self.assertEqual(result.changed, (path,))

    def test_compares_all_hash_sidecar_content(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            first_entries = minimal_entries()
            second_entries = minimal_entries()
            olean_hash = (
                "aeneas/backends/lean/.lake/build/lib/lean/Aeneas.olean.hash"
            )
            ilean_hash = (
                "aeneas/backends/lean/.lake/build/lib/lean/Aeneas.ilean.hash"
            )
            first_entries.extend(
                [(olean_hash, b"first", 0o444), (ilean_hash, b"first", 0o444)]
            )
            second_entries.extend(
                [(olean_hash, b"second", 0o444), (ilean_hash, b"second", 0o444)]
            )

            result = compare_toolchain_archives.compare_inventories(
                self.inspect(make_archive(directory, "first", first_entries)),
                self.inspect(make_archive(directory, "second", second_entries)),
            )
            self.assertEqual(result.changed, tuple(sorted((ilean_hash, olean_hash))))

    def test_compares_trace_dependency_and_output_hashes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            path = "aeneas/backends/lean/.lake/build/lib/lean/Aeneas.trace"
            first_entries = minimal_entries() + [(path, trace_bytes(), 0o444)]
            variants = {
                "dependency": trace_bytes(dep_hash="1111111111111111"),
                "output": trace_bytes(output_hash="2222222222222222"),
            }
            first = self.inspect(make_archive(directory, "first", first_entries))
            for index, (label, changed_trace) in enumerate(variants.items()):
                with self.subTest(label=label):
                    second_entries = minimal_entries() + [(path, changed_trace, 0o444)]
                    result = compare_toolchain_archives.compare_inventories(
                        first,
                        self.inspect(
                            make_archive(directory, f"second-{index}", second_entries)
                        ),
                    )
                    self.assertEqual(result.changed, (path,))

    def test_detects_build_output_and_executable_status_changes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            first_entries = minimal_entries()
            second_entries = minimal_entries()
            replace_file(
                second_entries,
                "aeneas/backends/lean/.lake/build/lib/lean/Aeneas.olean",
                b"different-olean",
                0o444,
            )
            replace_file(
                second_entries,
                "lean/lib/lean/Init.olean",
                b"lean-library",
                0o555,
            )

            first = self.inspect(make_archive(directory, "first", first_entries))
            second = self.inspect(make_archive(directory, "second", second_entries))
            result = compare_toolchain_archives.compare_inventories(first, second)

            self.assertFalse(result.equivalent)
            self.assertEqual(result.only_first, ())
            self.assertEqual(result.only_second, ())
            self.assertEqual(
                set(result.changed),
                {
                    "aeneas/backends/lean/.lake/build/lib/lean/Aeneas.olean",
                    "lean/lib/lean/Init.olean",
                },
            )

    def test_rejects_non_executable_required_command(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            entries = minimal_entries()
            replace_file(entries, "lean/bin/lean", b"lean-bin", 0o644)
            with self.assertRaisesRegex(
                compare_toolchain_archives.ArchiveInspectionError,
                "required commands are not executable",
            ):
                self.inspect(make_archive(directory, "non-executable", entries))

    def test_detects_non_aeneas_toolchain_payload_changes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            first_entries = minimal_entries()
            second_entries = minimal_entries()
            lean_path = "lean/lib/lean/Init.olean"
            rust_path = "rust/lib/rustlib/components"
            replace_file(second_entries, lean_path, b"different Lean library", 0o444)
            replace_file(second_entries, rust_path, b"different Rust components", 0o444)

            result = compare_toolchain_archives.compare_inventories(
                self.inspect(make_archive(directory, "first", first_entries)),
                self.inspect(make_archive(directory, "second", second_entries)),
            )
            self.assertEqual(set(result.changed), {lean_path, rust_path})

    def test_treats_hard_link_storage_as_equivalent_to_regular_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            first_entries = minimal_entries()
            second_entries = minimal_entries()
            output = "aeneas/backends/lean/.lake/build/lib/lean/Aeneas.olean"
            shared = "aeneas/backends/lean/.lake/build/lib/lean/Shared.olean"
            first_entries.append((shared, b"aeneas-olean", 0o444))
            second_entries.append((shared, b"aeneas-olean", 0o444))
            for index, entry in enumerate(second_entries):
                if entry[0] == output:
                    second_entries[index] = (output, shared, 0o444)
                    break
            else:
                self.fail("fixture output not found")

            first = self.inspect(make_archive(directory, "first", first_entries))
            second = self.inspect(make_archive(directory, "second", second_entries))
            result = compare_toolchain_archives.compare_inventories(first, second)
            self.assertTrue(result.equivalent)

    def test_metadata_path_and_mode_inventories_must_match(self) -> None:
        trace = "aeneas/backends/lean/.lake/build/lib/lean/Extra.trace"
        config = "aeneas/backends/lean/.lake/config/aeneas/extra.json"
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            metadata_entries = [
                (trace, trace_bytes(context="first"), 0o444),
                (config, b"first", 0o444),
            ]
            first_entries = minimal_entries() + metadata_entries
            changed_mode = minimal_entries() + [
                (trace, trace_bytes(context="second"), 0o644),
                (config, b"second", 0o444),
            ]
            first = self.inspect(make_archive(directory, "first", first_entries))

            mode_result = compare_toolchain_archives.compare_inventories(
                first, self.inspect(make_archive(directory, "mode", changed_mode))
            )
            self.assertEqual(mode_result.changed, (trace,))

            for index, missing_path in enumerate((trace, config)):
                with self.subTest(missing=missing_path):
                    missing_entries = minimal_entries() + [
                        entry for entry in metadata_entries if entry[0] != missing_path
                    ]
                    missing_result = compare_toolchain_archives.compare_inventories(
                        first,
                        self.inspect(
                            make_archive(directory, f"missing-{index}", missing_entries)
                        ),
                    )
                    self.assertEqual(missing_result.only_first, (missing_path,))

    def test_resolves_archive_input_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            archive = make_archive(directory, "archive", minimal_entries())
            link = directory / "nix-output-link.tar.zst"
            link.symlink_to(archive.name)
            inventory = self.inspect(link)
            self.assertIn("lean/bin/lean", inventory.semantic_files)

    def test_rejects_parent_relative_archive_member(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            entries = minimal_entries()
            entries.append(("../escape", b"bad", 0o644))
            archive = make_archive(directory, "unsafe", entries)
            with self.assertRaisesRegex(
                compare_toolchain_archives.ArchiveInspectionError,
                "path contains '\\.\\.'",
            ):
                self.inspect(archive)

    def test_rejects_forbidden_lake_and_primer_state(self) -> None:
        forbidden_paths = {
            "ltar": "aeneas/backends/lean/.lake/build/Aeneas.ltar",
            "cache": "aeneas/backends/lean/.lake/cache/artifacts/content.olean",
            "nobuild": (
                "aeneas/backends/lean/.lake/build/lib/lean/Aeneas.trace.nobuild"
            ),
            "primer temporary state": "aeneas/backends/lean/.anneal-tmp/output",
        }
        for index, (label, path) in enumerate(forbidden_paths.items()):
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                directory = Path(tmp)
                entries = minimal_entries() + [(path, b"forbidden", 0o444)]
                archive = make_archive(directory, f"forbidden-{index}", entries)
                with self.assertRaisesRegex(
                    compare_toolchain_archives.ArchiveInspectionError,
                    "forbidden",
                ):
                    self.inspect(archive)


if __name__ == "__main__":
    unittest.main()
