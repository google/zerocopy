# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check toolchain-probe reporting with a small, failing fake installation."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


PROBE = Path(__file__).resolve().with_name("probe_toolchain.sh")
RAW_STDOUT = b"tool stdout\xff\n"
RAW_STDERR = b"tool stderr\xfe\n"
VERSION = b"rustc 1.98.0-nightly (f8a08b688 2026-05-30)\n"


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

    def write_rustc(self, status):
        output = (VERSION.decode().rstrip("\n") if status == 0
                  else "tool stdout\\377")
        self.rustc.write_text(
            f"#!/bin/sh\nprintf '{output}\\n'\n"
            f"printf 'tool stderr\\376\\n' >&2\nexit {status}\n"
        )
        self.rustc.chmod(0o700)

    def invoke(
        self, *arguments, closed_stdout=False, closed_stderr=False
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
            ("stdout", closed_stdout), ("stderr", closed_stderr)
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

    def retained_probe(self, result, status, stdout=RAW_STDOUT):
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


if __name__ == "__main__":
    unittest.main()
