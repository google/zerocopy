# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import output


class OutputTests(unittest.TestCase):
    def test_identical_generation_preserves_timestamp_but_changed_bytes_are_written(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Generated.lean'
            output.write_text(path, '-- λ\n')
            os.utime(path, ns=(1000000000, 1000000000))
            before = path.stat()
            output.write_bytes(path, '-- λ\n'.encode('utf-8'))
            self.assertEqual(path.stat().st_mtime_ns, before.st_mtime_ns)
            self.assertEqual(path.stat().st_ino, before.st_ino)
            output.write_text(path, '-- changed λ\n')
            self.assertEqual(path.read_bytes(), '-- changed λ\n'.encode('utf-8'))
            self.assertNotEqual(path.stat().st_mtime_ns, before.st_mtime_ns)


if __name__ == '__main__':
    unittest.main()
