# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check toolchain-probe reporting with small synthetic installations."""

import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


PROBE = Path(__file__).resolve().with_name("probe_toolchain.sh")
ANNEAL_ROOT = PROBE.parent.parent
RAW_STDOUT = b"tool stdout\xff\n"
RAW_STDERR = b"tool stderr\xfe\n"
VERSION = b"rustc 1.98.0-nightly (f8a08b688 2026-05-30)\n"
CALLBACK_NOTE = (
    "note: anneal-rustc-capture: compiler analysis callback reached; "
    "verification not performed"
)


@unittest.skipUnless(os.name == "posix", "requires POSIX shell tools and pipes")
class ProbeReportingTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="anneal probe test ")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.installation = self.root / "installation with spaces"
        self.rustc = self.installation / "rust/bin/rustc"
        self.rustc.parent.mkdir(parents=True)
        self.environment = os.environ.copy()
        self.environment["TMPDIR"] = str(self.root)

    def write_executable(self, rel_path: str, body: str) -> Path:
        path = self.installation / rel_path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"#!/bin/sh\n{body}\n", encoding="utf-8")
        path.chmod(0o700)
        return path

    def write_rustc(self, status: int) -> None:
        output = (
            VERSION.decode().rstrip("\n")
            if status == 0
            else "tool stdout\\377"
        )
        self.write_executable(
            "rust/bin/rustc",
            f"printf '{output}\\n'\n"
            f"printf 'tool stderr\\376\\n' >&2\n"
            f"exit {status}",
        )

    def write_complete_fake_installation(
        self, include_callback_note: bool = True
    ) -> None:
        self.write_executable(
            "rust/bin/rustc",
            'if [ "${1:-}" = "--version" ]; then\n'
            '  printf "rustc 1.98.0-nightly (f8a08b688 2026-05-30)\\n"\n'
            "  exit 0\n"
            "fi\n"
            'while [ "$#" -gt 0 ]; do\n'
            '  if [ "$1" = "-o" ]; then\n'
            '    printf "rmeta" > "$2"\n'
            "    exit 0\n"
            "  fi\n"
            "  shift\n"
            "done\n"
            "exit 1",
        )
        self.write_executable(
            "rust/bin/rustdoc",
            'if [ "${1:-}" = "--version" ]; then\n'
            '  printf "rustdoc 1.98.0-nightly (f8a08b688 2026-05-30)\\n"\n'
            "  exit 0\n"
            "fi\n"
            'out_dir=""\n'
            'while [ "$#" -gt 0 ]; do\n'
            '  if [ "$1" = "--out-dir" ]; then\n'
            '    out_dir="$2"\n'
            "  fi\n"
            "  shift\n"
            "done\n"
            'mkdir -p "$out_dir/toolchain_probe"\n'
            'printf "Installed documentation probe.\\n" > '
            '"$out_dir/toolchain_probe/index.html"\n'
            'printf "fn\\n" > "$out_dir/toolchain_probe/fn.identity.html"',
        )
        self.write_executable(
            "lean/bin/lean",
            'if [ "${1:-}" = "--version" ]; then\n'
            '  printf "Lean (version 4.34.1, fake, Release)\\n"\n'
            "  exit 0\n"
            "fi\n"
            'test -s "${1:-}"',
        )
        self.write_executable(
            "rust/bin/cargo",
            'if [ "${1:-}" = "--version" ]; then\n'
            '  printf "cargo 1.98.0-nightly (f8a08b688 2026-05-30)\\n"\n'
            "  exit 0\n"
            "fi\n"
            'target_dir=""\n'
            'while [ "$#" -gt 0 ]; do\n'
            '  if [ "$1" = "--target-dir" ]; then\n'
            '    target_dir="$2"\n'
            "  fi\n"
            "  shift\n"
            "done\n"
            'mkdir -p "$target_dir/debug/deps"\n'
            'printf "rmeta" > '
            '"$target_dir/debug/deps/libtoolchain_probe-0001.rmeta"',
        )
        note_cmd = (
            f'printf "{CALLBACK_NOTE}\\n" >&2\n'
            if include_callback_note
            else ""
        )
        self.write_executable(
            "bin/anneal-rustc-capture",
            'if [ "${1:-}" = "--version" ]; then\n'
            '  printf "anneal-rustc-capture 0.2.0\\n"\n'
            "  exit 0\n"
            "fi\n"
            'while [ "$#" -gt 0 ]; do\n'
            '  if [ "$1" = "-o" ]; then\n'
            '    printf "rmeta" > "$2"\n'
            f"    {note_cmd}"
            "    exit 0\n"
            "  fi\n"
            "  shift\n"
            "done\n"
            "exit 1",
        )

    def invoke(
        self,
        *arguments,
        closed_stdout: bool = False,
        closed_stderr: bool = False,
    ):
        command = ["bash", str(PROBE), *map(str, arguments)]
        options = {
            "cwd": self.root,
            "env": self.environment,
            "timeout": 10,
        }
        streams = {"stdout": subprocess.PIPE, "stderr": subprocess.PIPE}
        writers = []
        # Closing the reader before spawning makes SIGPIPE independent of
        # scheduling or of how much output the fake tool writes.
        for name, closed in (
            ("stdout", closed_stdout),
            ("stderr", closed_stderr),
        ):
            if closed:
                reader, writer = os.pipe()
                os.close(reader)
                streams[name] = writer
                writers.append(writer)
        try:
            return subprocess.run(command, **streams, **options)
        finally:
            for writer in writers:
                os.close(writer)

    def retained_probe(self, result, status: int, stdout: bytes = RAW_STDOUT):
        directories = list(self.root.glob("anneal-toolchain-probe.*"))
        self.assertEqual(len(directories), 1)
        probe = directories[0]
        if result.stderr is not None:
            self.assertIn(
                b"Toolchain probe evidence retained at " + os.fsencode(probe),
                result.stderr,
            )
        self.assertEqual((probe / "rustc-version.stdout").read_bytes(), stdout)
        self.assertEqual(
            (probe / "rustc-version.stderr").read_bytes(), RAW_STDERR
        )
        self.assertEqual(
            (probe / "rustc-version.status").read_bytes(),
            f"{status}\n".encode(),
        )
        self.assertFalse((probe / "rustdoc-version.stdout").exists())

    def test_complete_installation_passes_and_cleans_probe_dir(self):
        self.write_complete_fake_installation(include_callback_note=True)
        result = self.invoke(self.installation)
        self.assertEqual(
            result.returncode,
            0,
            f"stdout={result.stdout!r}\nstderr={result.stderr!r}",
        )
        self.assertEqual(list(self.root.glob("anneal-toolchain-probe.*")), [])

    def test_driver_without_callback_note_fails_and_retains_probe(self):
        self.write_complete_fake_installation(include_callback_note=False)
        result = self.invoke(self.installation)
        self.assertNotEqual(result.returncode, 0)
        directories = list(self.root.glob("anneal-toolchain-probe.*"))
        self.assertEqual(len(directories), 1)
        self.assertIn(
            b"Toolchain probe evidence retained at "
            + os.fsencode(directories[0]),
            result.stderr,
        )

    def test_tool_failure_retains_raw_streams_and_status(self):
        self.write_rustc(47)
        result = self.invoke(self.installation)
        self.assertEqual(result.returncode, 47)
        self.assertEqual(result.stdout, RAW_STDOUT)
        self.assertIn(RAW_STDERR, result.stderr)
        self.retained_probe(result, 47)

    def test_tool_failure_takes_priority_over_closed_stdout(self):
        self.write_rustc(47)
        result = self.invoke(self.installation, closed_stdout=True)
        self.assertEqual(result.returncode, 47)
        self.assertIn(RAW_STDERR, result.stderr)
        self.retained_probe(result, 47)

    def test_successful_tool_cannot_hide_closed_stdout(self):
        self.write_rustc(0)
        result = self.invoke(self.installation, closed_stdout=True)
        self.assertNotEqual(result.returncode, 0)
        self.retained_probe(result, 0, stdout=VERSION)

    def test_tool_failure_takes_priority_over_closed_stderr(self):
        self.write_rustc(47)
        result = self.invoke(self.installation, closed_stderr=True)
        self.assertEqual(result.returncode, 47)
        self.assertEqual(result.stdout, RAW_STDOUT)
        self.retained_probe(result, 47)

    def test_tool_failure_takes_priority_over_both_closed_streams(self):
        self.write_rustc(47)
        result = self.invoke(
            self.installation, closed_stdout=True, closed_stderr=True
        )
        self.assertEqual(result.returncode, 47)
        self.retained_probe(result, 47)

    def test_malformed_installation_arguments(self):
        ordinary_file = self.root / "ordinary file"
        ordinary_file.write_text("not an installation directory")
        for arguments in (
            (),
            ("relative installation",),
            (self.root / "missing installation",),
            (ordinary_file,),
            (self.installation, "extra argument"),
        ):
            with self.subTest(arguments=arguments):
                result = self.invoke(*arguments)
                self.assertEqual(result.returncode, 2)
                self.assertEqual(result.stdout, b"")
                self.assertIn(b"usage:", result.stderr)
                self.assertEqual(
                    list(self.root.glob("anneal-toolchain-probe.*")), []
                )


class ProbeVersionParityTests(unittest.TestCase):
    def test_pinned_versions_match_repository_sources(self):
        probe_text = PROBE.read_text(encoding="utf-8")
        ir_text = (
            ANNEAL_ROOT / "trusted/rustc-capture/src/ir.rs"
        ).read_text(encoding="utf-8")
        lean_tc = (
            ANNEAL_ROOT / "trusted/lean/lean-toolchain"
        ).read_text(encoding="utf-8").strip()

        compiler_match = re.search(
            r'^pub const COMPILER_VERSION: &str = "([^"]+)";$',
            ir_text,
            re.MULTILINE,
        )
        self.assertIsNotNone(compiler_match)
        compiler_version = compiler_match.group(1)
        self.assertTrue(lean_tc.startswith("leanprover/lean4:v"))
        lean_version = lean_tc.removeprefix("leanprover/lean4:v")

        rust_re_match = re.search(
            r"^expected_rust_re='([^']+)'$", probe_text, re.MULTILINE
        )
        rustdoc_re_match = re.search(
            r"^expected_rustdoc_re='([^']+)'$", probe_text, re.MULTILINE
        )
        self.assertIsNotNone(rust_re_match)
        self.assertIsNotNone(rustdoc_re_match)
        escaped = (
            compiler_version.replace("\\", "\\\\")
            .replace(".", r"\.")
            .replace("(", r"\(")
            .replace(")", r"\)")
        )
        rust_re = rust_re_match.group(1)
        rustdoc_re = rustdoc_re_match.group(1)
        self.assertEqual(rust_re, f"^rustc {escaped}$")
        self.assertEqual(rustdoc_re, f"^rustdoc {escaped}$")
        self.assertIsNotNone(re.fullmatch(rust_re, f"rustc {compiler_version}"))
        self.assertIsNotNone(
            re.fullmatch(rustdoc_re, f"rustdoc {compiler_version}")
        )
        self.assertEqual(VERSION, f"rustc {compiler_version}\n".encode())
        self.assertIn(f"'Lean (version {lean_version},'", probe_text)


if __name__ == "__main__":
    unittest.main()
