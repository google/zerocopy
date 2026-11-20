# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

from pathlib import Path
import tempfile
import unittest
from injected import injected_crate


class InjectionTests(unittest.TestCase):
    def test_failure_cannot_mutate_checkout(self):
        with tempfile.TemporaryDirectory() as temporary:
            repository = Path(temporary)
            crate = repository / "zerocopy"
            crate.mkdir()
            original = b'[package]\nname = "fixture"\nversion = "0.0.0"\n'
            (crate / "Cargo.toml").write_bytes(original)
            (crate / "Cargo.lock").write_bytes(b"original lockfile")
            (repository / "tools" / "kani-macros").mkdir(parents=True)
            (crate / "target").mkdir()
            (crate / "target" / "stale").touch()
            with self.assertRaisesRegex(RuntimeError, "verification failed"):
                with injected_crate(repository) as snapshot:
                    self.assertNotEqual(snapshot, crate)
                    self.assertFalse((snapshot / "target").exists())
                    self.assertIn("cfg(kani)", (snapshot / "Cargo.toml").read_text())
                    (snapshot / "Cargo.lock").write_text("changed lockfile")
                    raise RuntimeError("verification failed")
            self.assertFalse(snapshot.exists())
            self.assertEqual((crate / "Cargo.toml").read_bytes(), original)
            self.assertEqual((crate / "Cargo.lock").read_bytes(), b"original lockfile")


if __name__ == "__main__":
    unittest.main()
