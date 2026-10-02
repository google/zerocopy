# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location("prepare", Path(__file__).parents[1] / "prepare.py")
prepare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prepare)


class PrepareTests(unittest.TestCase):
    def test_rejects_error_bearing_or_missing_llbc_status(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "crate.llbc"
            for status in [True, None, 0, "false"]:
                path.write_text(json.dumps({"has_errors": status, "translated": {}}))
                with self.assertRaises(ValueError):
                    prepare.check_llbc(path)
            path.write_text(json.dumps({"has_errors": False, "translated": {}}))
            prepare.check_llbc(path)

    def test_renames_only_second_dictionary(self):
        types = ('"markerCopyInst", "markerCopyInst"\n'
                 'markerCopyInst : core.marker.Copy Self\n'
                 'markerCopyInst : core.marker.Copy Self_NonZeroInner\n')
        funs = ('markerCopyInst := core.marker.CopyUsize\n'
                'markerCopyInst := core.num.niche_types.NonZeroUsizeInner.Insts.CoreMarkerCopy\n'
                'def util.max := body\n')
        new_types, new_funs = prepare.rename_copy_fields(types, funs)
        self.assertIn('"markerCopyInst", "innerCopyInst"', new_types)
        self.assertIn('markerCopyInst : core.marker.Copy Self\n', new_types)
        self.assertIn('innerCopyInst : core.marker.Copy Self_NonZeroInner\n', new_types)
        self.assertIn('markerCopyInst := core.marker.CopyUsize\n', new_funs)
        self.assertTrue(new_funs.endswith('def util.max := body\n'))
        # Upgrades, duplicate matches, and accidental repeated application fail.
        for bad_types, bad_funs in [(types + types, funs), (types, ''), (new_types, new_funs)]:
            with self.assertRaises(ValueError):
                prepare.rename_copy_fields(bad_types, bad_funs)

    def test_imports_include_public_meta_and_exclude_dependency_cache(self):
        with tempfile.TemporaryDirectory() as tmp:
            backend = Path(tmp)
            (backend / 'Aeneas.lean').write_text(
                'public import Mathlib.Data.BitVec\npublic meta import Mathlib.Tactic\n'
                'import Aeneas.Std\n')
            (backend / '.lake').mkdir()
            (backend / '.lake/Other.lean').write_text('import Mathlib\n')
            self.assertEqual(prepare.mathlib_imports(backend),
                             ['Mathlib.Data.BitVec', 'Mathlib.Tactic'])

    def test_imports_include_proof_modules_and_templates(self):
        with tempfile.TemporaryDirectory() as tmp:
            backend, proofs = Path(tmp) / 'backend', Path(tmp) / 'proofs'
            backend.mkdir()
            proofs.mkdir()
            (backend / 'Aeneas.lean').write_text('import Mathlib.Tactic.Basic\n')
            (proofs / 'RequiredContracts.lean').write_text(
                'public import Mathlib.Tactic.Convert\n')
            (proofs / 'Proofs.lean.in').write_text('import all Mathlib.Data.Nat.Log\n')
            self.assertEqual(prepare.mathlib_imports(backend, proofs),
                             ['Mathlib.Data.Nat.Log', 'Mathlib.Tactic.Basic',
                              'Mathlib.Tactic.Convert'])


if __name__ == '__main__':
    unittest.main()
