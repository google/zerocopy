# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import workspace


class WorkspaceTests(unittest.TestCase):
    def test_lake_uses_archive_policy_and_preserves_failure_status(self):
        for status in (0, 23):
            with self.subTest(status=status), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                marker = root / 'lake-call.json'
                lake = root / 'lake'
                lake.write_text('#!' + sys.executable + '\n' +
                                'import json,os,sys\nfrom pathlib import Path\n' +
                                'Path(' + repr(str(marker)) + ').write_text(json.dumps({"args":sys.argv[1:],"ci":os.environ.get("CI")}))\n' +
                                'print("unchanged Lake output")\n' +
                                'raise SystemExit(' + str(status) + ')\n')
                lake.chmod(0o755)
                command = ['lake', 'env', 'lean', '-DwarningAsError=true', 'Check.lean']
                output = io.StringIO()
                with mock.patch.dict(os.environ, CI='true', PATH=str(root) + os.pathsep + os.environ['PATH']), contextlib.redirect_stdout(output):
                    if status:
                        with self.assertRaises(subprocess.CalledProcessError) as error:
                            workspace.run_checked(command, root, root)
                        self.assertEqual(error.exception.returncode, status)
                    else:
                        workspace.run_checked(command, root, root)
                    self.assertEqual(os.environ['CI'], 'true')
                self.assertEqual(json.loads(marker.read_text()),
                                 {'args': ['--old', *command[1:]], 'ci': None})
                self.assertEqual(output.getvalue(), 'unchanged Lake output\n')

    def test_projection_edits_block_regeneration_with_copy_back_instructions(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            workspace.protect_projections(work)
            for module in workspace.PROJECTIONS:
                (work / f'{module}.lean').write_text(f'{module} original')
            workspace.record_projections(work)
            workspace.protect_projections(work)
            for module in workspace.PROJECTIONS:
                path = work / f'{module}.lean'
                original = path.read_bytes()
                path.write_text('manual construction or clause edit')
                before = {p.name: p.read_bytes() for p in work.iterdir()}
                with self.subTest(module=module), self.assertRaisesRegex(ValueError, 'Copy each authored fragment back') as error:
                    workspace.protect_projections(work)
                self.assertIn(f'{module}.source-map.json', str(error.exception))
                self.assertEqual(before, {p.name: p.read_bytes() for p in work.iterdir()})
                path.write_bytes(original)
            # Explicitly preserving and removing an edited projection permits regeneration.
            (work / 'Models.lean').unlink()
            workspace.protect_projections(work)

    def test_unbaselined_existing_projection_is_never_silently_adopted(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            (work / 'Specs.lean').write_text('unrecorded local changes')
            with self.assertRaisesRegex(ValueError, 'unbaselined'):
                workspace.protect_projections(work)
            self.assertFalse((work / workspace.PROJECTION_STATE).exists())
            (work / workspace.PROJECTION_STATE).write_text('{"version": 0}')
            with self.assertRaisesRegex(ValueError, 'Invalid projection baseline'):
                workspace.protect_projections(work)

    def test_inspection_rejects_wrong_binding_and_command_injection_before_running_lean(self):
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(workspace, 'run_checked') as run:
            work = Path(directory)
            (work / 'bindings.json').write_text('{"bindings": {}}')
            for candidate in ['missing', 'x\n#eval 1', 'Zerocopy.Proofs.foo']:
                with self.subTest(candidate=candidate), self.assertRaises(ValueError):
                    workspace.inspect_spec(work, work, candidate)
            run.assert_not_called()

    def test_fresh_projects_copy_proof_submodules_and_remove_stale_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = root / 'verification/aeneas/lean'
            for relative in ('Proofs.lean', 'Proofs/Util.lean', 'Specs.lean',
                             'Required.lean', 'lakefile.lean', 'Zerocopy/Funs.lean',
                             '.lake/packages/Dependency.lean'):
                path = sources / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(relative)
            backend = root / 'backend'
            backend.mkdir()
            (backend / 'lean-toolchain').write_text('leanprover/lean4:v4.31.0')
            work = root / 'target/aeneas/verification'
            work.mkdir(parents=True)
            (work / 'RemovedProof.lean').write_text('stale')
            workspace.initialize(root, work, backend)
            self.assertEqual({str(path.relative_to(work))
                              for path in work.rglob('*') if path.is_file()},
                             {'Proofs.lean', 'Proofs/Util.lean', 'lean-toolchain'})
            with self.assertRaises(ValueError):
                workspace.initialize(root, sources, backend)
            self.assertTrue((sources / 'Proofs/Util.lean').exists())

    def test_retires_only_recognized_legacy_generated_artifacts(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            old = work / 'Invariants.lean'
            mapping = work / 'Invariants.source-map.json'
            old.write_text(workspace.golden.HEADER + 'module\npublic import DeriveValidity\nnamespace Zerocopy.Invariants\nend Zerocopy.Invariants\n')
            mapping.write_text('{"17": {"file": "zerocopy/src/layout/mod.rs", "line": 42}}')
            workspace.retire_generated(work)
            self.assertFalse(old.exists())
            self.assertFalse(mapping.exists())
            old.write_text('handwritten source')
            with self.assertRaisesRegex(ValueError, 'Refusing to retire unrecognized'):
                workspace.retire_generated(work)
            self.assertEqual(old.read_text(), 'handwritten source')

    def test_model_support_discovers_all_root_and_nested_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = root / 'verification/aeneas/lean'
            (sources / 'ModelSupport').mkdir(parents=True)
            (sources / 'ModelSupport.lean').write_text('public import ModelSupport.Facts\n')
            (sources / 'ModelSupport/Facts.lean').write_text('public import SafeMath\n')
            (sources / 'SafeMath.lean').write_text('public import ModelShapes\n')
            self.assertEqual(workspace.model_support(root), ['ModelSupport', 'ModelSupport.Facts'])
            # Retired and current generated modules never become handwritten.
            for generated in ('Invariants.lean', 'ModelShapes.lean', 'Models.lean'):
                (sources / generated).write_text('obsolete')
            self.assertFalse(set(workspace.handwritten(root)) & {Path('Invariants.lean'), Path('Models.lean'), Path('ModelShapes.lean')})

    def test_handwritten_module_paths_do_not_conflate_literal_dotted_segments(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = root / 'verification/aeneas/lean'
            (sources / 'Helper').mkdir(parents=True)
            (sources / 'Helper/Name.lean').write_text('module\n')
            self.assertEqual(workspace.handwritten(root), [Path('Helper/Name.lean')])
            for filename in ('Helper.Name.lean', 'Helper Name.lean', '«Helper».lean'):
                path = sources / filename
                path.write_text('module\n')
                with self.subTest(filename=filename), self.assertRaisesRegex(ValueError, 'simple identifier components'):
                    workspace.handwritten(root)
                path.unlink()

    def test_diagnostics_preserve_lean_output_and_add_rust_location_on_failure(self):
        for module, kind in [('Specs', 'specification'), ('ModelShapes', 'model'), ('Models', 'model')]:
            with self.subTest(module=module), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                work = root / 'project'
                work.mkdir()
                (work / f'{module}.source-map.json').write_text(json.dumps({
                    '17': {'file': 'zerocopy/src/layout/mod.rs', 'line': 42}}))
                output = io.StringIO()
                message = f'{module}.lean:17:9: error: unknown identifier'
                command = [sys.executable, '-c',
                           f'print({message!r}); raise SystemExit(1)']
                with contextlib.redirect_stdout(output), self.assertRaises(
                        subprocess.CalledProcessError):
                    workspace.run_checked(command, root, work)
                self.assertIn(message, output.getvalue())
                self.assertIn(f'Inline {kind}: {root}/zerocopy/src/layout/mod.rs:42',
                              output.getvalue())


if __name__ == '__main__':
    unittest.main()
