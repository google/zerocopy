# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import importlib.util
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest

AENEAS = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('control_runner', AENEAS / 'control_runner.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class ControlRunnerTests(unittest.TestCase):
    def test_commands_preserve_raw_output_exact_status_and_elapsed(self):
        with tempfile.TemporaryDirectory() as temporary:
            logs = Path(temporary)
            for status in (0, 7):
                result = subprocess.run([sys.executable, str(AENEAS / 'control_runner.py'),
                    'command', str(logs), '--', sys.executable, '-c',
                    f'import os; os.write(1, b"out\\x00"); os.write(2,b"err"); raise SystemExit({status})'],
                    capture_output=True)
                self.assertEqual(result.returncode, status)
                self.assertEqual(result.stdout, b'out\x00err')
            rows = [json.loads(path.read_text()) for path in logs.glob('*.json')]
            self.assertEqual(sorted(row['returncode'] for row in rows), [0, 7])
            for row in rows:
                self.assertEqual(Path(row['log']).read_bytes(), b'out\x00err')
                self.assertGreaterEqual(row['elapsed_seconds'], 0)

    def test_repeated_clock_values_preserve_separate_command_logs_and_statuses(self):
        # Separate wrapper processes can have identical process-relative clocks.
        launch = ('import runpy, sys, time; time.monotonic_ns = lambda: 12345; '
                  'sys.argv = sys.argv[1:]; runpy.run_path(sys.argv[0], run_name="__main__")')
        expected = {0: b'first\x00', 7: b'second\n'}
        with tempfile.TemporaryDirectory() as temporary:
            logs = Path(temporary)
            for status, output in expected.items():
                child = f'import os; os.write(1, {output!r}); raise SystemExit({status})'
                result = subprocess.run([sys.executable, '-B', '-c', launch,
                    str(AENEAS / 'control_runner.py'), 'command', str(logs), '--',
                    sys.executable, '-c', child], cwd=logs, capture_output=True)
                self.assertEqual(result.returncode, status, result.stderr)
                self.assertEqual(result.stdout, output)
            rows = [json.loads(path.read_text()) for path in logs.glob('*.json')]
            self.assertEqual(len(rows), 2)
            self.assertEqual({row['returncode'] for row in rows}, set(expected))
            self.assertEqual(len(list(logs.glob('*.log'))), 2)
            self.assertEqual(len({row['log'] for row in rows}), 2)
            for row in rows:
                self.assertEqual(Path(row['log']).read_bytes(), expected[row['returncode']])

    def test_missing_executable_is_operational_failure_with_log(self):
        with tempfile.TemporaryDirectory() as temporary:
            result = subprocess.run([sys.executable, str(AENEAS / 'control_runner.py'),
                'command', temporary, '--', '/missing-aeneas-executable'], capture_output=True)
            self.assertEqual(result.returncode, 127)
            row, = [json.loads(p.read_text()) for p in Path(temporary).glob('*.json')]
            self.assertIsNone(row['returncode'])
            self.assertEqual(row['state'], 'launch-failed')
            self.assertIn(b'No such file', Path(row['log']).read_bytes())

    def test_clone_isolates_all_mutable_package_and_project_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            source = work / 'source'
            source.mkdir()
            mutable = work / 'mutable'
            (mutable / 'aeneas/.lake').mkdir(parents=True)
            (mutable / '.lake').mkdir(exist_ok=True)
            (source / '.lake/build').mkdir(parents=True)
            for p in (source, mutable, mutable / 'aeneas'):
                (p / 'lakefile.lean').write_text('config')
                (p / '.lake/lakefile.olean').write_text('original configuration')
                (p / '.lake/config/0').mkdir(parents=True)
                (p / '.lake/config/0/lakefile.olean').write_text('Lean 4.31 configuration')
                (p / '.lake/config/1').mkdir(parents=True)
                (p / '.lake/config/1/lakefile.olean.trace').write_text('Lean 4.31 config trace')
            (mutable / 'Rust.lean').write_text('baseline package')
            (source / 'Proofs.lean').write_text('baseline proof')
            (source / '.lake/build/proof.olean').write_text('baseline cache')
            (source / 'lake-manifest.json').write_text(json.dumps({'packages': [
                {'name': 'rust_model', 'dir': str(mutable)},
                {'name': 'rust_model_aeneas', 'dir': str(mutable / 'aeneas')},
                {'name': 'aeneas', 'dir': '/immutable/backend'}]}))
            (source / 'lakefile.lean').write_text(json.dumps(str(mutable)) + ' ' + json.dumps(str(mutable / 'aeneas')))
            first = runner.clone_project(source, work / 'first', mutable)
            second = runner.clone_project(source, work / 'second', mutable)
            (first / 'Proofs.lean').write_text('mutated')
            (first.parent / 'rust-model/Rust.lean').write_text('mutated package')
            runner.clear_mutable_outputs(first)
            self.assertEqual((source / 'Proofs.lean').read_text(), 'baseline proof')
            self.assertEqual((second / 'Proofs.lean').read_text(), 'baseline proof')
            self.assertEqual((second.parent / 'rust-model/Rust.lean').read_text(), 'baseline package')
            self.assertTrue((second / '.lake/build/proof.olean').exists())
            for p in (first, first.parent / 'rust-model', first.parent / 'rust-model/aeneas'):
                self.assertFalse((p / '.lake/lakefile.olean').exists())
                self.assertFalse((p / '.lake/config').exists())
            self.assertIn(str(first.parent / 'rust-model'), (first / 'lakefile.lean').read_text())
            self.assertIn('/immutable/backend', (first / 'lake-manifest.json').read_text())

    def test_leaf_eviction_retains_independent_audit_and_other_owner(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = Path(temporary)
            cache = project / '.lake/build/lib/lean'
            (cache / 'Zerocopy').mkdir(parents=True)
            for name in ('Zerocopy/Funs.olean', 'Zerocopy/Funs.ilean', 'Required.olean', 'Funs.olean'):
                (cache / name).write_text('cached')
            runner.clear_mutable_outputs(project, ['Zerocopy.Funs'])
            self.assertFalse((cache / 'Zerocopy/Funs.olean').exists())
            self.assertTrue((cache / 'Required.olean').exists())
            self.assertTrue((cache / 'Funs.olean').exists())

    def test_collects_every_family_after_failure_and_records_exact_status(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            tasks = []
            for status in (3, 0, 9):
                def prepare(status=status):
                    project = root / f'sandbox{status}/project'
                    project.mkdir(parents=True)
                    return project
                tasks.append((f'case{status}', prepare,
                    [sys.executable, '-c', f'raise SystemExit({status})'], lambda p, l: dict(os.environ)))
            rows, status = runner.run_families(tasks, 2, root / 'logs')
            self.assertEqual(status, 1)
            self.assertEqual(sorted(row['returncode'] for row in rows), [0, 3, 9])
            self.assertEqual(len(list((root / 'logs').rglob('status.json'))), 3)
            self.assertFalse(list(root.glob('sandbox*')))

    def test_preparation_failure_does_not_hide_another_family_result(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            def invalid():
                raise OSError('injected clone failure')
            def valid():
                project = root / 'sandbox/project'
                project.mkdir(parents=True)
                return project
            rows, status = runner.run_families([
                ('broken', invalid, ['true'], lambda p, l: dict(os.environ)),
                ('valid', valid, [sys.executable, '-c', 'raise SystemExit(0)'],
                 lambda p, l: dict(os.environ))], 2, root / 'logs')
            self.assertEqual(status, 1)
            self.assertEqual({row['family']: row['returncode'] for row in rows},
                             {'broken': None, 'valid': 0})
            self.assertEqual(rows[0]['state'], 'launch-failed')
            self.assertIn('injected clone failure', (root / 'logs/broken/family.log').read_text())

    def test_interruption_kills_family_group_and_does_not_start_pending_work(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            harness = root / 'harness.py'
            child = ('import os, signal, time; '
                     'signal.signal(signal.SIGTERM, signal.SIG_IGN); '
                     f'open({str(root / "child.pid")!r}, "w").write(str(os.getpid())); '
                     'time.sleep(3600)')
            harness.write_text(
                'import sys, os, json\nfrom pathlib import Path\n'
                f'sys.path.insert(0, {str(AENEAS)!r})\nimport control_runner as runner\n'
                f'root = Path({str(root)!r})\n'
                'def prepare():\n'
                '    project = root / "sandbox/project"\n'
                '    project.mkdir(parents=True)\n'
                '    return project\n'
                f'task = ("active", prepare, [sys.executable, "-c", {child!r}], '
                'lambda p, l: dict(os.environ))\n'
                'pending = ("pending", prepare, [sys.executable, "-c", "raise SystemExit(0)"], lambda p, l: dict(os.environ))\n'
                'rows, status = runner.run_families([task, pending], 1, root / "logs")\n'
                '(root / "result.json").write_text(json.dumps({"rows": rows, "status": status}))\n'
                'sys.exit(status)\n')
            process = subprocess.Popen([sys.executable, str(harness)], stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE)
            try:
                deadline = time.monotonic() + 5
                while not (root / 'child.pid').exists() and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue((root / 'child.pid').exists())
                process.send_signal(signal.SIGTERM)
                out, err = process.communicate(timeout=5)
                self.assertEqual(process.returncode, 143, out + err)
                result = json.loads((root / 'result.json').read_text())
                self.assertEqual(result['status'], 143)
                self.assertEqual(len(result['rows']), 2)
                self.assertEqual(result['rows'][1]['state'], 'cancelled')
                self.assertIsNone(result['rows'][1]['returncode'])
                self.assertEqual(result['rows'][0]['returncode'], -signal.SIGKILL)
                self.assertFalse((root / 'sandbox').exists())
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()

    def test_suite_interruption_during_baseline_stops_descendants_and_keeps_roster(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            native = root / 'verification/aeneas/lean'
            native.mkdir(parents=True)
            (root / 'anneal/lean/aeneas').mkdir(parents=True)
            for model in runner.MODELS:
                project = root / 'target/aeneas' / model
                project.mkdir(parents=True)
                (project / 'bindings.json').write_text(json.dumps({'mode': 'verified-live'}))
                (project / 'lake-manifest.json').write_text(json.dumps({'packages': []}))
                (project / 'lakefile.lean').write_text('-- fixture configuration')
            child = ('import os, signal, time; '
                     'signal.signal(signal.SIGTERM, signal.SIG_IGN); '
                     f'open({str(root / "descendant.pid")!r}, "w").write(str(os.getpid())); '
                     'time.sleep(3600)')
            (root / 'verification/aeneas/workspace.py').write_text(
                'import subprocess, sys, time\n'
                f'subprocess.Popen([sys.executable, "-c", {child!r}])\n'
                'time.sleep(3600)\n')
            harness = root / 'harness.py'
            harness.write_text('import sys\nfrom types import SimpleNamespace\n'
                f'sys.path.insert(0, {str(AENEAS)!r})\nimport control_runner as runner\n'
                f'sys.exit(runner.suite(SimpleNamespace(model=None, jobs=1), root={str(root)!r}))\n')
            process = subprocess.Popen([sys.executable, str(harness)], stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE)
            try:
                deadline = time.monotonic() + 5
                while not (root / 'descendant.pid').exists() and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue((root / 'descendant.pid').exists())
                descendant = int((root / 'descendant.pid').read_text())
                process.send_signal(signal.SIGTERM)
                out, err = process.communicate(timeout=7)
                self.assertEqual(process.returncode, 143, out + err)
                summary, = list((root / 'target/aeneas/control-logs').glob('run-*/summary.json'))
                report = json.loads(summary.read_text())
                self.assertEqual(report['returncode'], 143)
                self.assertEqual(len(report['families']), 1 + 2 * len(runner.FAMILIES))
                for row in report['families']:
                    self.assertEqual(row['state'], 'cancelled')
                    self.assertIsNone(row['returncode'])
                self.assertEqual(report['baselines'][0]['returncode'], -signal.SIGTERM)
                self.assertEqual(report['baselines'][1]['state'], 'cancelled')
                self.assertIsNone(report['baselines'][1]['returncode'])
                # A killed descendant can briefly remain a reparented zombie on
                # Linux. Its state must never be a running or sleeping process.
                if sys.platform.startswith('linux'):
                    try:
                        state = Path(f'/proc/{descendant}/stat').read_text().rsplit(')', 1)[1].split()[0]
                    except FileNotFoundError:
                        pass
                    else:
                        self.assertEqual(state, 'Z')
                else:
                    with self.assertRaises(ProcessLookupError):
                        os.kill(descendant, 0)
                self.assertFalse(list((root / 'target/aeneas').glob('control-sandboxes-*')))
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()

    def test_ci_preflight_accepts_native_trait_laws_and_rejects_projection_edits(self):
        sys.path.insert(0, str(AENEAS))
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / 'project'
            source.mkdir()
            native = root / 'verification/aeneas/lean'
            native.mkdir(parents=True)
            (native / 'SpecPrelude.lean').write_text('-- authored\n')
            shutil.copyfile(native / 'SpecPrelude.lean', source / 'SpecPrelude.lean')
            (source / 'bindings.json').write_text(json.dumps({'mode': 'verified-live'}))
            (source / 'TraitLaws.lean').write_text('theorem native_trait_law : True := by trivial\n')
            digests = {}
            for module in ('Specs', 'ModelShapes', 'Models'):
                text = (module + ' baseline\n').encode()
                (source / (module + '.lean')).write_bytes(text)
                digests[module] = hashlib.sha256(text).hexdigest()
            (source / '.inline-projections.json').write_text(json.dumps({'version': 1, 'sha256': digests}))
            runner.preflight(root, source)
            (source / '.inline-projections.json').unlink()
            runner.preflight(root, source)
            (source / 'bindings.json').write_text(json.dumps({'mode': 'development'}))
            with self.assertRaisesRegex(ValueError, 'verified-live CI bindings'):
                runner.preflight(root, source)
            (source / 'bindings.json').write_text(json.dumps({'mode': 'verified-live'}))
            (source / '.inline-projections.json').write_text(json.dumps({'version': 1, 'sha256': digests}))
            (source / 'Models.lean').write_text('edited projection')
            with self.assertRaisesRegex(ValueError, 'Edited generated projection'):
                runner.preflight(root, source)
            self.assertEqual((source / 'Models.lean').read_text(), 'edited projection')

    def test_semantic_rejection_cannot_be_satisfied_by_operational_status(self):
        controls = (AENEAS / 'negative-control-family.sh').read_text()
        start = 'expect_failure() {\n'
        body = controls.split(start, 1)[1].split('\n}\n', 1)[0]
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            harness = work / 'harness.sh'
            harness.write_text('set -euo pipefail\nbackup=$PWD\n' + start + body + '\n}\n'
                'expect_failure fixture rejection.log python3 -c '
                "'print(\"error: intended diagnostic\"); raise SystemExit(127)'\n")
            result = subprocess.run(['bash', str(harness)], cwd=work, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'failed operationally (status=127)', result.stderr)
            self.assertNotIn(b'Confirmed: rejected', result.stdout)

    def test_fresh_build_rejects_proof_with_unchanged_source_and_changed_import(self):
        lake = shutil.which('lake')
        if not lake:
            self.skipTest('Requires the pinned Lean installation')
        with tempfile.TemporaryDirectory() as temporary:
            project = Path(temporary)
            (project / 'lean-toolchain').write_bytes((AENEAS.parents[1] / 'anneal/lean/lean-toolchain').read_bytes())
            (project / 'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage freshness\nlean_lib Model\n@[default_target] lean_lib Required\n')
            model = project / 'Model.lean'
            model.write_text('def accepted : Nat := 0\n')
            proof = project / 'Required.lean'
            proof.write_text('import Model\ntheorem baseline : accepted = 0 := rfl\n')
            env = dict(os.environ)
            env.pop('CI', None)
            positive = subprocess.run([lake, '--old', 'build'], cwd=project, env=env, capture_output=True)
            self.assertEqual(positive.returncode, 0, positive.stdout + positive.stderr)
            proof_bytes = proof.read_bytes()
            old_stat = model.stat()
            model.write_text('def accepted : Nat := 1\n')
            os.utime(model, ns=(old_stat.st_atime_ns, old_stat.st_mtime_ns))
            reject = subprocess.run([sys.executable, str(AENEAS / 'control_runner.py'),
                'command', '--fresh', str(project / 'logs'), '--', 'lake', '--old', 'build', 'Required'],
                cwd=project, env=env, capture_output=True)
            self.assertNotEqual(reject.returncode, 0)
            self.assertIn(b'Required.lean', reject.stdout, reject.stderr)
            self.assertIn(b'type mismatch', reject.stdout.lower())
            self.assertEqual(proof.read_bytes(), proof_bytes)
            row, = [json.loads(p.read_text()) for p in (project / 'logs').glob('*.json')]
            self.assertEqual((Path(row['sources']) / 'Model.lean').read_bytes(), model.read_bytes())
            self.assertEqual((Path(row['sources']) / 'Required.lean').read_bytes(), proof_bytes)



class FamilyShellTests(unittest.TestCase):
    def run_family_header(self, scenario, expected_status, source_overrides=None):
        """Execute the production setup/wrapper/EXIT trap, without Lean builds."""
        controls = (AENEAS / 'negative-control-family.sh').read_text()
        boundary = '\n# This helper checks command failure, not its semantic cause. Each control\n'
        self.assertEqual(controls.count(boundary), 1)
        header = controls.split(boundary, 1)[0]
        completion = 'control_complete=yes\n)\ncheck_workspace "$AENEAS_CONTROL_MODEL"\n'
        self.assertTrue(controls.endswith(completion))
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            aeneas = root / 'verification/aeneas'
            aeneas.mkdir(parents=True)
            (aeneas / 'toolchain.sh').write_text(':\n')
            (aeneas / 'control_runner.py').write_text(
                'import json, os, sys\nfrom pathlib import Path\n'
                'Path(os.environ["CONTROL_ARGUMENT_LOG"]).write_text(json.dumps(sys.argv[1:]))\n')
            project = root / 'project'
            (project / 'Zerocopy').mkdir(parents=True)
            sources = dict.fromkeys(('bindings.json', 'Required.lean', 'Specs.lean', 'ModelShapes.lean',
                         'Models.lean', 'SpecPrelude.lean', 'Obligations.lean',
                         'Zerocopy/Funs.lean', 'Zerocopy/FunsExternal.lean'), 'baseline\n')
            sources.update(source_overrides or {})
            for name, text in sources.items():
                (project / name).parent.mkdir(parents=True, exist_ok=True)
                (project / name).write_text(text)
            script = aeneas / 'negative-control-family.sh'
            # Retain the actual completion statement and final invocation too.
            script.write_text(header + '\n' + scenario + '\n' + completion)
            env = dict(os.environ, AENEAS_CONTROL_REPO=str(root),
                       AENEAS_CONTROL_PROJECT=str(project),
                       AENEAS_CONTROL_LOG_DIR=str(root / 'logs'),
                       AENEAS_CONTROL_MODEL='verification',
                       AENEAS_CONTROL_FAMILY='shell-regression',
                       CONTROL_ARGUMENT_LOG=str(root / 'arguments.json'))
            result = subprocess.run(['/bin/bash', str(script)], env=env,
                                    capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, expected_status, result.stdout + result.stderr)
            arguments = root / 'arguments.json'
            return (result, json.loads(arguments.read_text()) if arguments.exists() else None,
                    (project / 'Specs.lean').read_text(),
                    (project / 'NegativeControl.lean').exists())

    def test_dependency_fixture_reads_actual_baseline_sources_directory(self):
        import ast
        controls = (AENEAS / 'negative-control-family.sh').read_text()
        start = '    padding_dependency_fixture() {\n'
        self.assertEqual(controls.count(start), 1)
        body = controls.split(start, 1)[1].split('\n    }\n', 1)[0]
        helper = start + body + '\n    }\n'
        python = body.split("<<'PYCONTROL'\n", 1)[1].split('\nPYCONTROL', 1)[0]
        values = {node.targets[0].id: ast.literal_eval(node.value)
                  for node in ast.parse(python).body
                  if isinstance(node, ast.Assign) and len(node.targets) == 1
                  and isinstance(node.targets[0], ast.Name)
                  and node.targets[0].id in ('header', 'body', 'callee_header', 'registration')}
        self.assertEqual(set(values), {'header', 'body', 'callee_header', 'registration'})
        # Use the real backup machinery and real dependency fixture helper.
        # Tiny source payloads satisfy its framing checks without compiling Lean.
        sources = {
            'Proofs/ArithmeticChecks.lean': ('module\n@[expose] public section\n' +
                                           values['header'] + values['body']),
            'Proofs/Util.lean': (values['callee_header'] + '\n  exact Raw.padding_lt_alignment\n' +
                                values['registration']),
            'Required.lean': 'def auditModuleNames : Array Name := #[]\n',
        }
        scenario = (helper + '\n[[ ! -f "$backup/Proofs/ArithmeticChecks.lean" ]]\n'
                    'padding_dependency_fixture direct\n'
                    "grep -Fq 'exact And.left' Proofs/ArithmeticChecks.lean\n")
        self.run_family_header(scenario, 0, source_overrides=sources)

    def test_nonbuild_command_uses_production_wrapper_without_empty_array(self):
        result, argv, _, _ = self.run_family_header(
            'aeneas_lake env lean -DwarningAsError=true Check.lean', 0)
        self.assertEqual(argv[0], 'command')
        self.assertNotIn('--fresh', argv)
        self.assertEqual(argv[2:], ['--', 'lake', '--old', 'env', 'lean',
                                   '-DwarningAsError=true', 'Check.lean'])
        self.assertNotIn('unbound variable', result.stderr)

    def test_build_command_uses_production_wrapper_with_fresh_outputs(self):
        _, argv, _, _ = self.run_family_header('aeneas_lake build Required', 0)
        self.assertEqual(argv[:2], ['command', '--fresh'])
        self.assertEqual(argv[3:], ['--', 'lake', '--old', 'build', 'Required'])

    def test_fatal_nounset_in_actual_family_header_cannot_report_success(self):
        scenario = ('unset unavailable_control_value\n'
                    'fatal_nounset() { printf "%s" "$unavailable_control_value"; }\n'
                    'fatal_nounset')
        result, _, _, _ = self.run_family_header(scenario, 1)
        self.assertIn('unbound variable', result.stderr)
        version = subprocess.run(['/bin/bash', '--version'], capture_output=True, text=True).stdout
        if 'version 3.2.' in version:
            # This diagnostic requires the real EXIT trap to have received zero.
            self.assertIn('family exited before completing its controls', result.stderr)

    def test_regular_nonzero_status_survives_actual_family_cleanup(self):
        result, _, restored, fixture_exists = self.run_family_header(
            'printf "mutant\n" > Specs.lean\n'
            'touch NegativeControl.lean\nexit 7', 7)
        self.assertEqual(restored, 'baseline\n')
        self.assertFalse(fixture_exists)
        self.assertNotIn('cleanup failed', result.stderr)

    def test_failed_source_restore_prevents_completed_family_success(self):
        result, _, _, _ = self.run_family_header('restore_files() { return 23; }', 23)
        self.assertIn('cleanup failed (status=23)', result.stderr)

    def test_failed_fixture_removal_prevents_completed_family_success(self):
        result, _, _, _ = self.run_family_header('rm() { return 24; }', 24)
        self.assertIn('cleanup failed (status=24)', result.stderr)

    def test_original_failure_status_survives_cleanup_failure(self):
        result, _, _, _ = self.run_family_header('restore_files() { return 23; }\nexit 7', 7)
        self.assertIn('cleanup failed (status=23)', result.stderr)

    def test_exit_zero_before_actual_completion_statement_fails_closed(self):
        result, _, _, _ = self.run_family_header('exit 0', 1)
        self.assertIn('family exited before completing its controls', result.stderr)


if __name__ == '__main__':
    unittest.main()
