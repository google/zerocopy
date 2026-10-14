# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import workspace


class WorkspaceTests(unittest.TestCase):
    def test_development_checks_select_native_modules_without_a_final_audit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            work = root / 'project'
            work.mkdir()
            (work / 'lakefile.lean').write_text('import Lake\n')
            (work / 'Proofs').mkdir()
            (work / 'Proofs/Padding.lean').write_text('theorem padding : True := trivial\n')
            output = io.StringIO()
            with mock.patch.object(workspace, 'run_checked') as run, contextlib.redirect_stdout(output):
                workspace.develop(root, work, ['Proofs.Padding'])
                run.assert_called_once_with(['lake', 'build', '+Proofs.Padding:olean'], root, work, archive=False)
            self.assertIn('PROVISIONAL', output.getvalue())
            self.assertIn('final golden/live verification', output.getvalue())
            for invalid in ['../Proofs/Padding', 'Proofs.Missing', 'aeneas']:
                with self.subTest(invalid=invalid), mock.patch.object(workspace, 'run_checked') as run:
                    with self.assertRaisesRegex(ValueError, 'local Lean modules'):
                        workspace.develop(root, work, [invalid])
                    run.assert_not_called()

    def test_dev_script_checks_without_module_targets_on_host_bash(self):
        # Bash 3.2 treats expansion of an empty array as nounset. Exercise both
        # real shell branches; stub compiler/generator work unrelated to argv.
        aeneas = Path(workspace.__file__).resolve().parent
        for prepared in (False, True):
            with self.subTest(prepared=prepared), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                scripts = root / 'verification/aeneas'
                scripts.mkdir(parents=True)
                shutil.copyfile(aeneas / 'dev.sh', scripts / 'dev.sh')
                shutil.copyfile(aeneas / 'output.py', scripts / 'output.py')
                (scripts / 'toolchain.sh').write_text('AENEAS_LEAN_TOOLCHAIN=test-pin\n')
                (scripts / 'run.sh').write_text('echo development-extraction\n')
                (scripts / 'golden.py').write_text('def files(*args, **kwargs): return []\n')
                (scripts / 'workspace.py').write_text('import sys\nprint("WORKSPACE", sys.argv[1:])\n')
                for name in ('inline.py', 'prepare.py'):
                    (scripts / name).write_text('# Test stub for generation.\n')
                if prepared:
                    work = scripts / 'lean'
                    work.mkdir()
                    (work / 'lakefile.lean').write_text('import Lake\n')
                tools = root / 'tools'
                backend = tools / 'backends/lean'
                backend.mkdir(parents=True)
                (backend / 'lean-toolchain').write_text('test-pin\n')
                binaries = tools / 'lean/bin'
                binaries.mkdir(parents=True)
                cargo = binaries / 'cargo'
                cargo.write_text('#!/bin/sh\nexit 0\n')
                cargo.chmod(0o755)
                result = subprocess.run(['/bin/bash', str(scripts / 'dev.sh'), '--check'],
                    env=dict(os.environ, AENEAS_TOOLCHAIN_DIR=str(tools)),
                    capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("WORKSPACE ['develop',", result.stdout)
                self.assertNotIn('--target', result.stdout)
                self.assertNotIn('unbound variable', result.stderr)

    def test_final_verification_rejects_development_target_options(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            result = subprocess.run([sys.executable, str(Path(workspace.__file__).resolve()),
                                     'verify', str(root), '--root', str(root), '--target', 'Proofs'],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertIn('only for provisional development', result.stderr)
            self.assertEqual(list(root.iterdir()), [])

    def test_incremental_development_rejects_a_proof_after_an_import_changes(self):
        if shutil.which('lake') is None:
            self.skipTest('Requires the pinned Lean installation')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pin = Path(__file__).resolve().parents[3] / 'anneal/lean/lean-toolchain'
            (root / 'lean-toolchain').write_bytes(pin.read_bytes())
            (root / 'lakefile.lean').write_text('import Lake\nopen Lake DSL\n'
                'package zerocopyVerification\n'
                '@[default_target] lean_lib Model\n@[default_target] lean_lib Proof\n')
            model = root / 'Model.lean'
            model.write_text('def modeled : Nat := 0\n')
            proof = root / 'Proof.lean'
            proof.write_text('import Model\ntheorem modeled_spec : modeled = 0 := by rfl\n')
            with contextlib.redirect_stdout(io.StringIO()):
                workspace.develop(root, root, ['Proof'])
                before = (root / '.lake/build/lib/lean/Proof.olean').stat().st_mtime_ns
                workspace.develop(root, root, ['Proof'])
                self.assertEqual((root / '.lake/build/lib/lean/Proof.olean').stat().st_mtime_ns, before)
                timestamp = model.stat()
                model.write_text('def modeled : Nat := 1\n')
                os.utime(model, ns=(timestamp.st_atime_ns, timestamp.st_mtime_ns))
                with self.assertRaises(subprocess.CalledProcessError):
                    workspace.develop(root, root, ['Proof'])

    def test_ci_verification_cannot_accept_development_bindings(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for mode in (None, 'development', 'verified', ''):
                (root / 'bindings.json').write_text(json.dumps({'mode': mode}))
                with self.subTest(mode=mode), mock.patch.object(workspace, 'run_checked') as run:
                    with self.assertRaisesRegex(ValueError, 'CI verification requires verified-live'):
                        workspace.check(root, root, require_admission=True)
                    run.assert_not_called()

    def test_verified_check_requires_both_admission_stages_and_fresh_inputs(self):
        # These are acceptance-path controls: no proof compilation may start
        # when admission is absent, incomplete, stale, or bound to other roots.
        import copy
        import admission
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            work = root / 'project'
            work.mkdir()
            manifest = {'mode': 'verified-live', 'sources': 'source',
                        'bindings': {'crate::f': {'kind': 'function'}},
                        'admission': {'version': 1, 'sources': 'source',
                                      'registry': 'registry', 'inputs': {'project': 'current'},
                                      'stages': {stage: {'roots': ['crate::f']}
                                                 for stage in ('before', 'llbc')}}}
            mutants = []
            mutant = copy.deepcopy(manifest)
            del mutant['admission']
            mutants.append(mutant)
            for stage in ('before', 'llbc'):
                mutant = copy.deepcopy(manifest)
                del mutant['admission']['stages'][stage]
                mutants.append(mutant)
                mutant = copy.deepcopy(manifest)
                mutant['admission']['stages'][stage]['roots'] = []
                mutants.append(mutant)
            for key, value in [('sources', 'other'), ('registry', 'other'),
                               ('inputs', {'project': 'old'})]:
                mutant = copy.deepcopy(manifest)
                mutant['admission'][key] = value
                mutants.append(mutant)
            with mock.patch.object(admission, 'input_identity', return_value={'project': 'current'}), \
                    mock.patch.object(admission, 'digest', return_value='registry'), \
                    mock.patch.object(workspace, 'run_checked') as run:
                for mutant in mutants:
                    (work / 'bindings.json').write_text(json.dumps(mutant))
                    with self.subTest(mutant=mutant), self.assertRaisesRegex(ValueError, 'admission evidence'):
                        workspace.check(root, work)
                    run.assert_not_called()
                (work / 'bindings.json').write_text(json.dumps(manifest))
                workspace.check(root, work)
                self.assertEqual(run.call_count, 3)
                run.reset_mock()
                # An editor changing Rust during a successful proof build must
                # prevent that build from certifying the edited source.
                with mock.patch.object(admission, 'input_identity',
                                       side_effect=[{'project': 'current'}, {'project': 'edited'}]):
                    with self.assertRaisesRegex(ValueError, 'Inputs changed during proof'):
                        workspace.check(root, work)
                    self.assertEqual(run.call_count, 3)
                run.reset_mock()
                # Fresh extraction fingerprints do not establish freshness of
                # the Lean sources copied before those fingerprints were made.
                source = root / 'verification/aeneas/lean/Helper.lean'
                source.parent.mkdir(parents=True)
                source.write_text('def helper : Nat := 1\n')
                copied = work / 'Helper.lean'
                for contents in (None, 'def helper : Nat := 0\n'):
                    if contents is not None:
                        copied.write_text(contents)
                    with self.subTest(contents=contents), self.assertRaisesRegex(
                            ValueError, 'CI proof source differs'):
                        workspace.check(root, work, require_admission=True)
                    run.assert_not_called()
                copied.write_bytes(source.read_bytes())
                workspace.check(root, work, require_admission=True)
                self.assertEqual(run.call_count, 3)
                run.reset_mock()
                # A change to a copied source during compilation is also an
                # editor experiment, not verification of the checkout.
                def edit_copy(*_args):
                    copied.write_text('def helper : Nat := 2\n')
                run.side_effect = edit_copy
                with self.assertRaisesRegex(ValueError, 'CI proof source differs'):
                    workspace.check(root, work, require_admission=True)
                self.assertEqual(run.call_count, 3)

    def test_check_rejects_proof_cached_against_an_earlier_model(self):
        lake = shutil.which('lake')
        if lake is None:
            self.skipTest('Requires the pinned Lean installation')
        for package in ('frozen', 'rust_model', 'rust_model_aeneas'):
            mutable = package != 'frozen'
            with self.subTest(package=package), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                relative = {'frozen': 'frozen', 'rust_model': 'anneal/lean',
                            'rust_model_aeneas': 'anneal/lean/aeneas'}[package]
                dependency = root / relative
                project = root / 'project'
                dependency.mkdir(parents=True)
                project.mkdir()
                (project / 'bindings.json').write_text(json.dumps({'mode': 'development'}))
                pin = Path(__file__).resolve().parents[3] / 'anneal/lean/lean-toolchain'
                for work in (dependency, project):
                    (work / 'lean-toolchain').write_bytes(pin.read_bytes())
                (dependency / 'lakefile.lean').write_text(
                    f'import Lake\nopen Lake DSL\npackage {package}\n'
                    '@[default_target] lean_lib Frozen\n')
                (dependency / 'Frozen.lean').write_text('def frozen : Nat := 0\n')
                if package == 'rust_model':
                    # The intermediate stack has this package in the checkout,
                    # but only rust_model belongs to its generated project.
                    unused = root / 'anneal/lean/aeneas/lakefile.lean'
                    unused.parent.mkdir()
                    unused.write_text('import Lake\nopen Lake DSL\npackage rust_model_aeneas\n')
                env = dict(os.environ)
                env.pop('CI', None)
                built = subprocess.run([lake, '--old', 'build'], cwd=dependency, env=env,
                                       capture_output=True, text=True, timeout=60)
                self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
                before = {str(p.relative_to(dependency)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in dependency.rglob('*') if p.is_file()}
                if not mutable:
                    for path in dependency.rglob('*'):
                        path.chmod(0o555 if path.is_dir() else 0o444)
                    dependency.chmod(0o555)
                (project / 'lakefile.lean').write_text(
                    'import Lake\nopen Lake DSL\n' +
                    f'require {package} from "../{dependency.relative_to(root)}"\n'
                    'package zerocopyVerification where\n'
                    '  moreLeanArgs := #["-DwarningAsError=true"]\n'
                    '@[default_target] lean_lib Model\n@[default_target] lean_lib Proof\n')
                model = project / 'Model.lean'
                model.write_text('import Frozen\ndef modeled : Nat := frozen + 1\n')
                proof = project / 'Proof.lean'
                proof.write_text('import Model\ntheorem modeled_spec : modeled = 1 := by rfl\n')
                (project / 'Check.lean').write_text('import Proof\n#check modeled_spec\n')
                # Assemble Lake's dependency manifest before checking, as the
                # real workspace generator does. Start with cached proofs too.
                built = subprocess.run([lake, '--old', 'build'], cwd=project, env=env,
                                       capture_output=True, text=True, timeout=60)
                self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
                output = io.StringIO()
                try:
                    with contextlib.redirect_stdout(output):
                        workspace.check(root, project)
                    proof_before = proof.read_bytes(), proof.stat().st_mtime_ns
                    if mutable:
                        shared = dependency / 'Frozen.lean'
                        previous = shared.stat()
                        shared.write_text('def frozen : Nat := 2\n')
                        # An archive or checkout can preserve source mtimes.
                        # Dependency cleaning must protect against that cache.
                        os.utime(shared, ns=(previous.st_atime_ns, previous.st_mtime_ns))
                    else:
                        model.write_text('import Frozen\ndef modeled : Nat := 2\n')
                    # Axiom inspection of a cached imported theorem cannot detect
                    # this inconsistency. Check must compile the proof source again.
                    with contextlib.redirect_stdout(output), self.assertRaises(
                            subprocess.CalledProcessError) as rejected:
                        workspace.check(root, project)
                    self.assertIn('build', rejected.exception.cmd)
                    self.assertIn('rfl', output.getvalue())
                    self.assertEqual((proof.read_bytes(), proof.stat().st_mtime_ns), proof_before)
                    after = {str(p.relative_to(dependency)): hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in dependency.rglob('*') if p.is_file()}
                    if not mutable:
                        self.assertEqual(after, before)
                finally:
                    dependency.chmod(0o755)
                    for path in dependency.rglob('*'):
                        if path.is_dir():
                            path.chmod(0o755)

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
