# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Compile harmless direct and transitive imports with the installed Lean.

Import reachability supplies dependency evidence, not semantic independence.
The arbitrary-outcome contract checks carry the latter obligation separately.
"""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
TOOLCHAIN = Path(os.environ.get('AENEAS_TOOLCHAIN_DIR', str(ROOT / 'target/aeneas/toolchain')))
LEAN = TOOLCHAIN / 'lean/bin/lean'


@unittest.skipUnless(LEAN.is_file(), 'requires installed pinned Lean')
class CompiledImportGraphTests(unittest.TestCase):
    def test_harmless_function_imports_are_ordinary_acyclic_dependencies(self):
        # Importing a function does not establish an operation expectation. The
        # arbitrary-outcome adequacy checks provide that semantic boundary.
        check = (ROOT / 'verification/aeneas/lean/Check.lean').read_text()
        self.assertNotIn('ModelSupport cannot depend', check)
        with tempfile.TemporaryDirectory(prefix='aeneas-import-graph-') as directory:
            work = Path(directory)
            env = dict(os.environ, LEAN_PATH=str(work))

            def compile_module(name, imports, body=''):
                path = work / (name.replace('.', '/') + '.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('module\n' + ''.join('public import ' + imported + '\n' for imported in imports) + body)
                result = subprocess.run([str(LEAN), '-o', str(path.with_suffix('.olean')), str(path)],
                                        cwd=work, env=env, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

            compile_module('ModelShapes', [])
            compile_module('Zerocopy.Funs', [], '@[expose] public def harmless (x : Nat) := x\n')
            compile_module('Zerocopy.FunsExternal', [], '@[expose] public def externalData := 3\n')
            for imported in ('Zerocopy.Funs', '«Zerocopy».Funs', '«Zerocopy».FunsExternal'):
                for transitive in (False, True):
                    with self.subTest(imported=imported, transitive=transitive):
                        compile_module('SafeMath', [imported] if transitive else ['ModelShapes'])
                        compile_module('ModelSupport', ['SafeMath'] if transitive else [imported])
                        compile_module('ModelSupport.Nested', [imported])
                        compile_module('Consumer', ['ModelSupport', 'ModelSupport.Nested'],
                                       'example : harmless 2 = 2 := rfl\n' if 'FunsExternal' not in imported else
                                       'example : externalData = 3 := rfl\n')


if __name__ == '__main__':
    unittest.main()
