# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location("prepare", Path(__file__).parents[1] / "prepare.py")
prepare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prepare)


class PrepareTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('lake'), 'Lake is required to elaborate its configuration')
    def test_generated_lake_configuration_passes_backend_option(self):
        # String checks cannot tell whether Lake accepts its configuration.
        # Elaborate the actual generated file and inspect the dependency's
        # option, without fetching packages or compiling their modules.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            backend, work, model = (root / name for name in ('backend with spaces', 'work', 'model'))
            for directory in (backend, work, model, model / 'aeneas'):
                directory.mkdir(parents=True, exist_ok=True)
            for directory, name in ((backend, 'aeneas'), (model, 'rust_model'),
                                    (model / 'aeneas', 'rust_model_aeneas')):
                (directory / 'lakefile.lean').write_text(
                    'import Lake\nopen Lake DSL\npackage ' + name + '\n')
            (backend / 'lake-manifest.json').write_text(json.dumps({
                'version': '1.2.0', 'packages': [],
            }))
            prepare.share_manifest(work, backend, model)
            lakefile = work / 'lakefile.lean'
            with lakefile.open('a') as file:
                file.write('\n#eval show IO Unit from do\n'
                           '  unless rust_model_aeneas.opts.find? `aeneasPath == some '
                           + json.dumps(str(backend)) + ' do\n'
                           '    throw (IO.userError "Incorrect backend option")\n')
            # Lake initializes the configuration DSL; direct Lean does not.
            # An environment command loads package configurations without
            # building modules. Match the archive consumers' Lake policy.
            env = dict(os.environ)
            env.pop('CI', None)
            result = subprocess.run(['lake', '--old', 'env', sys.executable, '-c', 'pass'],
                                    cwd=work, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_nominal_fixture_accepts_pruned_unused_dependency(self):
        script = (Path(__file__).parents[1] / 'tests/nominal-tuples.sh').read_text()
        code = script.split("<<'PYLEAN'\n", 1)[1].split('\nPYLEAN\n', 1)[0]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            backend, mathlib, cli = (root / name for name in ('backend', 'mathlib', 'Cli'))
            backend.mkdir()
            (mathlib / '.lake/build/lib/lean').mkdir(parents=True)
            cli.mkdir()  # The actual archive prunes Cli's unused compiled modules.
            manifest = {'packages': [
                {'type': 'path', 'dir': '../mathlib'},
                {'type': 'path', 'dir': '../Cli'},
            ]}
            (backend / 'lake-manifest.json').write_text(json.dumps(manifest))
            command = [sys.executable, '-', str(backend), str(root / 'generated')]
            result = subprocess.run(command, input=code, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip().split(os.pathsep), [
                str(root / 'generated'), str(backend / '.lake/build/lib/lean'),
                str(mathlib / '.lake/build/lib/lean'), str(cli / '.lake/build/lib/lean')])
            cli.rmdir()
            result = subprocess.run(command, input=code, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Missing pinned Lean dependency', result.stderr)

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

    def test_imports_include_native_proof_submodules(self):
        with tempfile.TemporaryDirectory() as tmp:
            backend, proofs = Path(tmp) / 'backend', Path(tmp) / 'proofs'
            backend.mkdir()
            proofs.mkdir()
            (backend / 'Aeneas.lean').write_text('import Mathlib.Tactic.Basic\n')
            (proofs / 'RequiredContracts.lean').write_text(
                'public import Mathlib.Tactic.Convert\n')
            (proofs / 'Proofs').mkdir()
            (proofs / 'Proofs/Helpers.lean').write_text('import all Mathlib.Data.Nat.Log\n')
            self.assertEqual(prepare.mathlib_imports(backend, proofs),
                             ['Mathlib.Data.Nat.Log', 'Mathlib.Tactic.Basic',
                              'Mathlib.Tactic.Convert'])

    def test_workspace_uses_vendored_manifest_paths(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            backend, work, model = (root / name for name in ('backend', 'work', 'model'))
            for directory in (backend, work, model, model / 'aeneas', root / 'vendor/mathlib'):
                directory.mkdir(parents=True, exist_ok=True)
            for directory in (model, model / 'aeneas'):
                (directory / 'lakefile.lean').write_text('')
            manifest = {'version': '1.2.0', 'packages': [{
                'type': 'path', 'name': 'mathlib', 'dir': '../vendor/mathlib',
                'inherited': False,
            }]}
            (backend / 'lake-manifest.json').write_text(json.dumps(manifest))
            prepare.share_manifest(work, backend, model)
            actual = json.loads((work / 'lake-manifest.json').read_text())
            dependency = next(p for p in actual['packages'] if p['name'] == 'mathlib')
            self.assertEqual(dependency, {
                'type': 'path', 'name': 'mathlib', 'dir': str((root / 'vendor/mathlib').resolve()),
                'inherited': True,
            })
            manifest['packages'][0]['type'] = 'git'
            (backend / 'lake-manifest.json').write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'vendored Lean path'):
                prepare.share_manifest(work, backend, model)
            manifest['packages'][0]['type'] = 'path'
            manifest['packages'][0]['dir'] = '../missing'
            (backend / 'lake-manifest.json').write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'Missing pinned Lean'):
                prepare.share_manifest(work, backend, model)

    def test_workspace_discovers_all_assembled_modules(self):
        with tempfile.TemporaryDirectory() as tmp:
            backend, work = Path(tmp) / 'backend', Path(tmp) / 'work'
            backend.mkdir()
            work.mkdir()
            (backend / 'lake-manifest.json').write_text(json.dumps({
                'version': '1.2.0', 'packages': [],
            }))
            for module in ('Specs', 'Invariants', 'Required', 'Zerocopy',
                           'ExtraGenerated', 'Check'):
                (work / (module + '.lean')).write_text('')
            rust_model = Path(tmp) / "rust-model"
            rust_model.mkdir()
            (rust_model / "lakefile.lean").write_text("")
            (rust_model / "aeneas").mkdir()
            (rust_model / "aeneas/lakefile.lean").write_text("")
            prepare.share_manifest(work, backend, rust_model)
            manifest = json.loads((work / 'lake-manifest.json').read_text())
            self.assertEqual(manifest['packages'][1]['name'], 'rust_model')
            self.assertEqual(manifest['packages'][1]['dir'], str(rust_model))
            config = (work / 'lakefile.lean').read_text()
            self.assertIn('require rust_model from ', config)
            self.assertEqual(manifest['packages'][2]['name'], 'rust_model_aeneas')
            self.assertEqual(manifest['packages'][2]['dir'], str(rust_model / 'aeneas'))
            self.assertIn('require rust_model_aeneas from ', config)
            self.assertIn('  Lean.NameMap.insert {} `aeneasPath ' + json.dumps(str(backend)), config)
            for module in ('Specs', 'Invariants', 'Required', 'Zerocopy',
                           'ExtraGenerated'):
                self.assertIn('@[default_target] lean_lib ' + module + '\n', config)
            self.assertIn('\nlean_lib Check\n', config)
            self.assertNotIn('@[default_target] lean_lib Check', config)


if __name__ == '__main__':
    unittest.main()
