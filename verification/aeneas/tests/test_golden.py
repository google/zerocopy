# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check the comparator's admission boundary independently of Lean builds.

These fixtures distinguish permitted presentation changes from code, literal,
and module-roster changes. A passing comparator test cannot replace compilation
of the golden and live proof projects.
"""

import importlib.util
import tempfile
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    "golden", Path(__file__).parents[1] / "golden.py")
golden = importlib.util.module_from_spec(spec)
spec.loader.exec_module(golden)


class GoldenTests(unittest.TestCase):
    def test_accepts_comments_blank_lines_and_trailing_whitespace(self):
        before = 'def min := do\n  if x > y\n  then ok y\n  else ok x\n'
        after = ('-- generated source moved\n\n'
                 '/-- source location /- nested comment -/ -/\n'
                 'def min := do  \t\n  if x > y -- explanation\n\n'
                 '  then ok y\n  else ok x\n')
        self.assertEqual(golden.normalize(before), golden.normalize(after))
        self.assertEqual(golden.normalize('x/- short -/y'),
                         golden.normalize('x/- much longer -/y'))
        self.assertNotEqual(golden.normalize('x/- comment -/y'),
                            golden.normalize('xy'))

    def test_preserves_code_structure_and_literal_contents(self):
        before = 'def min := do\n  if x > y\n  then ok y\n  else ok x\n'
        for after in [before.replace('>', '<'), before.replace('ok y', 'ok x'),
                      before.replace('  then', ' then'),
                      before.replace('if x', 'if  x'),
                      before.replace('then ok y\n  else', 'then ok y else')]:
            self.assertNotEqual(golden.normalize(before), golden.normalize(after))
        for literal in ['"-- /- spaces  -/"', '"a\\\"--b"', "'\"'",
                        '«-- /- spaces  -/»', '"a\n\n  \nb"']:
            self.assertEqual(golden.normalize('def s := ' + literal),
                             ['def s := ' + part if i == 0 else part
                              for i, part in enumerate(literal.split('\n'))])
        self.assertNotEqual(golden.normalize('def s := "a  "'),
                            golden.normalize('def s := "a "'))
        self.assertNotEqual(golden.normalize('def s := "a\n\nb"'),
                            golden.normalize('def s := "a\nb"'))

    def test_rejects_malformed_or_unsupported_literals(self):
        for source in ['/- unclosed', '"unclosed', '«unclosed', '"escape\\',
                       'r#"raw"#', 's!"interpolated"']:
            with self.assertRaises(ValueError):
                golden.normalize(source)

    def test_full_file_set_and_template_signatures_are_checked(self):
        with tempfile.TemporaryDirectory() as tmp:
            live, snapshot = Path(tmp) / 'live', Path(tmp) / 'golden'
            live.mkdir()
            for name in golden.FILES:
                (live / name).write_text('def x := 1\n')
            for name in golden.HANDWRITTEN:
                (live / name).write_text('def external := 2\n')
            golden.update(live, snapshot)
            self.assertEqual(golden.compare(live, snapshot), [])
            self.assertTrue((snapshot / 'Types.lean').read_text().startswith('/- Copyright'))
            original = {name: (snapshot / name).read_bytes() for name in golden.FILES}
            (live / 'Funs.lean').write_text('def x := "unclosed\n')
            with self.assertRaises(ValueError):
                golden.update(live, snapshot)
            self.assertEqual(original,
                             {name: (snapshot / name).read_bytes() for name in golden.FILES})
            (live / 'Funs.lean').write_text('def x := 1\n')
            (live / 'TypesExternal_Template.lean').write_text('def x := 2\n')
            self.assertTrue(golden.compare(live, snapshot))
            (live / 'Types.lean').unlink()
            with self.assertRaises(ValueError):
                golden.compare(live, snapshot)
            (live / 'Types.lean').write_text('def x := 1\n')
            (live / 'New.lean').write_text('def extra := 1\n')
            with self.assertRaises(ValueError):
                golden.compare(live, snapshot)
            (live / 'New.lean').unlink()
            (snapshot / 'Unexpected.lean').write_text('def extra := 1\n')
            with self.assertRaises(ValueError):
                golden.compare(live, snapshot)


if __name__ == '__main__':
    unittest.main()
