# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

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
    def test_production_audit_uses_resolved_direct_transitive_and_nested_imports(self):
        check = (ROOT / 'verification/aeneas/lean/Check.lean').read_text()
        begin = '  -- Model-support import closure is audited from compiled module identities.\n'
        end = '  let layoutInputs :='
        self.assertEqual(check.count(begin), 1)
        self.assertEqual(check.count(end), 1)
        audit_body = check[check.index(begin):check.index(end)]
        with tempfile.TemporaryDirectory(prefix='aeneas-import-graph-') as directory:
            work = Path(directory)
            env = dict(os.environ, LEAN_PATH=str(work))

            def compile_module(name, imports):
                path = work / (name.replace('.', '/') + '.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('module\n' + ''.join('public import ' + imported + '\n' for imported in imports))
                result = subprocess.run([str(LEAN), '-o', str(path.with_suffix('.olean')), str(path)],
                                        cwd=work, env=env, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

            def audit(extra=''):
                path = work / 'Audit.lean'
                path.write_text('import Lean\nimport ModelSupport\n' + extra +
                                'open Lean Elab Command\nrun_elab do\n  let env ← getEnv\n' + audit_body)
                return subprocess.run([str(LEAN), str(path)], cwd=work, env=env,
                                      capture_output=True, text=True)

            forbidden = [('«Zerocopy».Funs', 'Zerocopy.Funs'),
                         ('«Zerocopy».FunsExternal', 'Zerocopy.FunsExternal'),
                         ('«Proofs».Child', 'Proofs.Child'), ('«Models»', 'Models'),
                         ('«Specs»', 'Specs'), ('«Invariants»', 'Invariants')]
            for module in ['ModelShapes', *(name for _, name in forbidden)]:
                compile_module(module, [])
            compile_module('SafeMath', ['ModelShapes'])
            compile_module('ModelSupport', ['«SafeMath»'])
            result = audit()
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            for spelling, name in forbidden:
                for transitive in (False, True):
                    with self.subTest(module=name, transitive=transitive):
                        compile_module('SafeMath', [spelling] if transitive else ['ModelShapes'])
                        compile_module('ModelSupport', ['«SafeMath»'] if transitive else [spelling])
                        result = audit()
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn('ModelSupport cannot depend', result.stdout + result.stderr)
                        self.assertIn(name, result.stdout + result.stderr)
            compile_module('ModelSupport', ['ModelShapes'])
            compile_module('ModelSupport.Nested', ['«Zerocopy».Funs'])
            result = audit('import ModelSupport.Nested\n')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('ModelSupport cannot depend', result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
