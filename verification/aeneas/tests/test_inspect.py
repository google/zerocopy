# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Read-only inspection regression against an explicitly selected compiled project.

AENEAS_INSPECTION_PROJECT=/path/to/compiled/project python3 -B -m unittest
    discover -s verification/aeneas/tests -p test_inspect.py
"""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
PROJECT = os.environ.get('AENEAS_INSPECTION_PROJECT')


@unittest.skipUnless(PROJECT, 'Set AENEAS_INSPECTION_PROJECT to reuse compiled prerequisites')
class InspectTests(unittest.TestCase):
    def test_compiled_provider_mode_ghosts_and_rejection(self):
        source = (ROOT / 'verification/aeneas/lean/InspectSpec.lean').read_text()
        source = source.replace('import Specs\n', 'import Specs\nimport SpecsSyntaxTests\n')
        # Positive prerequisites are imported compiled modules. Guarded failures
        # must identify the intended call/decoding audit, rather than imports.
        source += '''
inspect_spec SpecsSyntaxTests.word_partial
/-- error: Specification SpecsSyntaxTests.word_partial does not call the expected model SpecsSyntaxTests.nativeIdentity -/
#guard_msgs (error, drop info) in
check_spec_binding SpecsSyntaxTests.word_partial for SpecsSyntaxTests.nativeIdentity with 1
inspect_spec SpecsSyntaxTests.fixed_provider_spec
inspect_spec SpecsSyntaxTests.generic_fixed
inspect_spec SpecsSyntaxTests.model_dependent_ghost
namespace InspectionRegression
open Aeneas.Std AeneasSpecs
def original (x : Nat) : Result Nat := .ok x
@[aeneas_spec] abbrev wrongCall : Prop :=
  ∀ x : Nat, WP.spec (original (x + 1)) (fun _ => True)
/-- error: Specification InspectionRegression.wrongCall model input 1 is not its original bound variable -/
#guard_msgs (error, drop info) in
inspect_spec wrongCall
@[aeneas_spec] abbrev missingDecode : Prop :=
  ∀ x : Nat, WP.spec (original x) (fun _ => True)
/-- error: Specification InspectionRegression.missingDecode lacks the expected decoded-result existential -/
#guard_msgs (error, drop info) in
inspect_spec missingDecode
@[aeneas_spec] abbrev rejectedDecode : Prop :=
  ∀ x : Nat, WP.spec (original x) (fun raw => ∃ math : Nat,
    @RustModel.decode Nat modelNat raw = none ∧ math = math)
/-- error: Specification InspectionRegression.rejectedDecode does not require successful decoding of its original result -/
#guard_msgs (error, drop info) in
inspect_spec rejectedDecode
end InspectionRegression
'''
        with tempfile.TemporaryDirectory(prefix='aeneas-inspection-test-') as directory:
            path = Path(directory) / 'Regression.lean'
            path.write_text(source)
            result = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', str(path)],
                                    cwd=PROJECT, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Execution: partial (WP.dspec)', result.stdout)
        self.assertIn('Execution: total (WP.spec)', result.stdout)
        self.assertIn('modelNat', result.stdout)
        self.assertIn('position', result.stdout)
        self.assertIn('constraint', result.stdout)
        self.assertIn('Required result decoding:', result.stdout)
        self.assertIn('Original raw call:', result.stdout)
        # The competing ghost must not be reported as the selected input provider.
        self.assertNotIn('Selected provider: evil', result.stdout)
        self.assertNotIn('Selected result provider: evil', result.stdout)


if __name__ == '__main__':
    unittest.main()
