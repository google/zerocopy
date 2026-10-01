# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import source_inventory


class SourceInventoryTests(unittest.TestCase):
    def test_links_cannot_hide_or_externalize_source(self):
        for location in ('zerocopy', 'zerocopy/src', 'zerocopy/src/linked', 'zerocopy/src/linked.rs'):
            for dangling in (False, True):
                with self.subTest(location=location, dangling=dangling), tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    external = root / 'external'
                    if not dangling:
                        external.mkdir()
                    link = root / location
                    link.parent.mkdir(parents=True, exist_ok=True)
                    link.symlink_to(external, target_is_directory=True)
                    with self.assertRaisesRegex(ValueError, 'Symbolic links'):
                        source_inventory.crate_files(root)

    def test_missing_or_unreadable_sources_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with self.assertRaisesRegex(ValueError, 'Missing mandatory source tree'):
                source_inventory.crate_files(root)
            (root / 'zerocopy/src').mkdir(parents=True)

            def unreadable(_path, *, onerror):
                onerror(PermissionError('unreadable module'))

            with mock.patch.object(source_inventory.os, 'walk', side_effect=unreadable):
                with self.assertRaisesRegex(ValueError, 'Cannot inspect the mandatory source tree'):
                    source_inventory.crate_files(root)
