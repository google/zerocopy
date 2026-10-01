# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class NegativeControlTests(unittest.TestCase):
    def test_predicate_control_rechecks_unchanged_outcome_source(self):
        lake = shutil.which('lake')
        if lake is None:
            self.skipTest('Requires the pinned Lean installation')
        aeneas = Path(__file__).resolve().parents[1]
        controls = (aeneas / 'negative-controls.sh').read_text()
        # These four production functions have unindented closing braces.
        # Extract only their exact bodies; fail if that boundary changes.
        functions = []
        for name in ('restore_files', 'expect_failure', 'check_model_mutant',
                     'reject_predicate'):
            start = name + '() {\n'
            self.assertEqual(controls.count(start), 1, name)
            _, tail = controls.split(start)
            body, end, _ = tail.partition('\n}\n')
            self.assertTrue(end, name)
            functions.append(start + body + end)
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            backup = work / 'backup'
            backup.mkdir()
            pin = aeneas.parents[1] / 'anneal/lean/lean-toolchain'
            (work / 'lean-toolchain').write_bytes(pin.read_bytes())
            (work / 'lakefile.lean').write_text(
                'import Lake\nopen Lake DSL\npackage predicateControl where\n'
                '  moreLeanArgs := #["-DwarningAsError=true"]\n'
                '@[default_target] lean_lib LayoutModel\n'
                '@[default_target] lean_lib OutcomeTests\n')
            model = work / 'LayoutModel.lean'
            model.write_text('def castSpec (x : Nat) : Prop := x = 0\n'
                             'def endOfPredicates : Nat := 0\n')
            outcomes = work / 'OutcomeTests.lean'
            outcomes.write_text('import LayoutModel\n'
                                'theorem rejects_one : ¬ castSpec 1 := by simp [castSpec]\n')
            for source in (model, outcomes):
                (backup / source.name).write_bytes(source.read_bytes())
            (work / 'bindings.json').write_text('{}\n')
            (backup / 'bindings.json').write_text('{}\n')
            env = dict(os.environ)
            env.pop('CI', None)
            built = subprocess.run([lake, '--old', 'build'], cwd=work, env=env,
                                   capture_output=True, text=True, timeout=60)
            self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
            self.assertTrue((work / '.lake/build/lib/lean/OutcomeTests.olean').is_file())
            baseline = outcomes.read_bytes()
            harness = work / 'control.sh'
            # Exercise Lake's production archive policy without sourcing the
            # toolchain installer or claiming this tiny fixture admits a cache.
            harness.write_text('set -euo pipefail\nbackup=$PWD/backup\n'
                               'aeneas_lake() (\n    unset CI\n'
                               '    command lake --old "$@"\n)\n' +
                               '\n'.join(functions) +
                               '\nreject_predicate castSpec True OutcomeTests\n')
            checked = subprocess.run(['bash', str(harness)], cwd=work, env=env,
                                     capture_output=True, text=True, timeout=60)
            log = (backup / 'outcome-test.log').read_text()
            self.assertEqual(checked.returncode, 0,
                             checked.stdout + checked.stderr + log)
            self.assertIn('Confirmed: rejected a changed mathematical predicate castSpec',
                          checked.stdout)
            self.assertIn('OutcomeTests.lean:', log)
            self.assertIn('error:', log)
            self.assertIn('unsolved goals', log)
            self.assertNotIn('Malformed model negative control', checked.stderr)
            self.assertEqual(outcomes.read_bytes(), baseline)
            self.assertEqual(model.read_bytes(), (backup / model.name).read_bytes())


if __name__ == '__main__':
    unittest.main()
