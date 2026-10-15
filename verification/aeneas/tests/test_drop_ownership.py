# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check the complete-snapshot boundary for empty conditional-drop proofs.

Small, self-contained compiler-schema bodies exercise both extraction stages.
Installed-runtime tests build the actual Lean checker and witness command;
Python-only controls keep binding and missing-proof rejection covered without
an installed runtime. These fixtures do not execute Rust or establish the
compiler correspondence premise of the ownership model.
"""

import copy
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'verification/aeneas'))
import admission
import drop_ownership

TOOLS = Path(os.environ.get('AENEAS_TOOLCHAIN_DIR',
                            str(ROOT / 'target/aeneas/toolchain'))).resolve()
LEAN = TOOLS / 'lean/bin/lean'
ROOT_NAME = 'zerocopy::empty_drop_test'
FUNCTION_ID = 7


def body_fixture(stage='Unstructured', move='Move'):
    """Move the argument into the return slot, then conditionally drop it."""
    boolean = {'Untagged': {'Scalar': 'Bool'}}
    span = {'Untagged': {'data': {'file_id': 0,
            'beg': {'line': 1, 'col': 0}, 'end': {'line': 1, 'col': 1}},
            'generated_from_span': None}}
    generics = {'regions': [], 'types': [], 'const_generics': [], 'trait_refs': []}

    def place(index):
        return {'kind': {'Local': index}, 'ty': copy.deepcopy(boolean)}

    def statement(kind, index=0):
        result = {'span': span, 'kind': kind, 'comments_before': []}
        if stage == 'Structured':
            result['id'] = index
        return result

    assignment = {'Assign': [place(0), {'Use': [{move: place(1)}, 'Yes']}]}
    dropped = {'kind': 'Conditional', 'place': place(1),
               'fn_ptr': {'kind': {'Fun': 99}, 'generics': generics}}
    if stage == 'Unstructured':
        dropped.update(target=1, on_unwind=2)
        contents = [
            {'statements': [statement(assignment)],
             'terminator': statement({'Drop': dropped})},
            {'statements': [], 'terminator': statement('Return')},
            {'statements': [], 'terminator': statement('UnwindResume')},
        ]
    elif stage == 'Structured':
        dropped['on_unwind'] = {'span': span, 'id': 1,
                               'statements': [statement('UnwindResume', 2)]}
        contents = {'span': span, 'id': 0, 'statements': [
            statement(assignment), statement({'Drop': dropped}, 1),
            statement('Return', 3)]}
    else:
        raise ValueError(stage)
    return {stage: {'span': span, 'bound_body_regions': 0,
        'locals': {'arg_count': 1, 'locals': [
            {'index': index, 'name': None, 'span': span,
             'ty': copy.deepcopy(boolean), 'drop_flag_for': None}
            for index in range(2)]},
        'body': contents, 'comments': []}}


def function_fixture(stage='Unstructured', move='Move'):
    return {'def_id': FUNCTION_ID, 'body': body_fixture(stage, move)}


def snapshot_bytes(function, **extra):
    return json.dumps({'has_errors': False,
        'translated': {'fun_decls': [function]}, **extra}, sort_keys=True).encode()


def admission_fixture(stage='Unstructured', move='Move'):
    # Reuse only the checked-in compiler option and declaration scaffolding.
    # This leaf root needs no external interpretations or executable callees.
    fixture = Path(__file__).with_name('admission') / 'boolean.before.ullbc'
    data = json.loads(fixture.read_text())
    function = next(f for f in data['translated']['fun_decls'] if f)
    function['def_id'] = FUNCTION_ID
    function['item_meta']['name'] = [{'Ident': [part, 0]}
                                    for part in ROOT_NAME.split('::')]
    function['item_meta']['attr_info']['attributes'] = []
    function['signature'] = {'is_unsafe': False, 'abi': 'Rust',
        'is_variadic': False, 'inputs': [{'Untagged': {'Scalar': 'Bool'}}],
        'output': {'Untagged': {'Scalar': 'Bool'}}}
    function['body'] = body_fixture(stage, move)
    crate = data['translated']
    crate['fun_decls'] = [function]
    crate['trait_impls'] = []
    crate['options']['exclude'] = list(admission.EXCLUDED_PROVIDED_METHODS)
    crate['options']['opaque'] = [admission.INTERFACE_ONLY_VALIDATORS,
                                   *admission.INTERFACE_ONLY_TYPES]
    return data, function


def recheck_fixture(work):
    """Write both stage inputs and their saved source-identity records."""
    registry = json.loads((ROOT / 'verification/aeneas/external.json').read_text())
    reports = {}
    for stage, tag, filename in (
            ('before', 'Unstructured', 'zerocopy.before.ullbc'),
            ('llbc', 'Structured', 'zerocopy.llbc')):
        data, function = admission_fixture(tag)
        # inspect_stages uses the production registry. This leaf fixture does
        # not call any of its boundaries, but must preserve its option profile.
        data['translated']['options']['opaque'] += [row['rust'] for row in registry
                                                  if row.get('opaque')]
        contents = json.dumps(data).encode()
        (work / filename).write_bytes(contents)
        snapshot = hashlib.sha256(contents).hexdigest()
        reports[stage] = {'roots': [ROOT_NAME], 'calls': [],
            'executions': [{'rust': ROOT_NAME, 'origin': 'body'}],
            'sha256': snapshot, 'empty_drops': [{
                'function_def_id': FUNCTION_ID,
                'body_sha256': drop_ownership.body_digest(function['body']),
                'snapshot_sha256': snapshot,
                'proof_module': 'old_witness_' + stage, 'proof_sha256': 'old-artifact'}]}
    return {'bindings': {ROOT_NAME: {'kind': 'function'},
                         'unused::Type': {'kind': 'type'}},
            'trait_laws': [], 'admission': {'stages': reports}}


class DropBindingTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix='aeneas-drop-binding-')
        self.addCleanup(self.scratch.cleanup)
        self.driver = drop_ownership.KernelDrops(ROOT, Path(self.scratch.name))

    def test_body_substitution_with_same_native_id_is_rejected_before_lean(self):
        original = function_fixture()
        self.driver.freeze('before', snapshot_bytes(original))
        for replacement in (function_fixture(move='Copy'),
                            {'def_id': FUNCTION_ID, 'body': {'fabricated': []}}):
            with self.subTest(body=replacement['body']):
                with mock.patch.object(self.driver, 'initialize'), \
                        mock.patch.object(self.driver, 'run') as run:
                    with self.assertRaisesRegex(ValueError, 'differs from the inspected'):
                        self.driver.certify('before', replacement)
                    run.assert_not_called()

    def test_duplicate_native_ids_are_rejected_before_lean(self):
        function = function_fixture()
        contents = json.dumps({'has_errors': False, 'translated': {
            'fun_decls': [function, copy.deepcopy(function)]}}).encode()
        self.driver.freeze('before', contents)
        with mock.patch.object(self.driver, 'initialize'), \
                mock.patch.object(self.driver, 'run') as run:
            with self.assertRaisesRegex(ValueError, 'differs from the inspected'):
                self.driver.certify('before', function)
            run.assert_not_called()

    def test_admission_requires_a_certificate_callback(self):
        for stage in ('Unstructured', 'Structured'):
            data, _ = admission_fixture(stage)
            with self.subTest(stage=stage):
                with self.assertRaisesRegex(ValueError, 'requires a kernel-checked compiler body'):
                    admission.Admission(data, []).audit([ROOT_NAME])

    def test_admission_rejects_a_certificate_for_another_body(self):
        data, function = admission_fixture(move='Copy')
        stale = {'function_def_id': FUNCTION_ID,
                 'body_sha256': drop_ownership.body_digest(body_fixture())}
        self.assertNotEqual(stale['body_sha256'],
                            drop_ownership.body_digest(function['body']))
        with self.assertRaisesRegex(ValueError, 'does not identify this exact compiler body'):
            admission.Admission(data, [], certify_drops=lambda _: stale).audit([ROOT_NAME])

    def test_admission_propagates_certificate_failure(self):
        data, _ = admission_fixture()

        def rejected(_):
            raise ValueError('kernel proof failed')

        with self.assertRaisesRegex(ValueError, 'kernel proof failed'):
            admission.Admission(data, [], certify_drops=rejected).audit([ROOT_NAME])


class DropRecheckTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix='aeneas-drop-recheck-')
        self.addCleanup(self.scratch.cleanup)
        self.work = Path(self.scratch.name)
        self.manifest = recheck_fixture(self.work)
        self.fresh = copy.deepcopy(self.manifest['admission']['stages'])

    def test_missing_empty_or_duplicate_proof_records_are_rejected(self):
        for stage in ('before', 'llbc'):
            for mutation in ('missing', 'empty', 'duplicate', 'not-list'):
                saved = copy.deepcopy(self.manifest)
                report = saved['admission']['stages'][stage]
                if mutation == 'missing':
                    del report['empty_drops']
                elif mutation == 'empty':
                    report['empty_drops'] = []
                elif mutation == 'duplicate':
                    report['empty_drops'] *= 2
                else:
                    report['empty_drops'] = None
                with self.subTest(stage=stage, mutation=mutation):
                    with mock.patch.object(admission, 'inspect_stages', return_value=self.fresh):
                        with self.assertRaisesRegex(ValueError, 'proof records|admission evidence'):
                            admission.recheck(ROOT, self.work, saved)

    def test_missing_or_stale_body_and_snapshot_identities_are_rejected(self):
        for stage in ('before', 'llbc'):
            for key in ('function_def_id', 'body_sha256', 'snapshot_sha256'):
                for mutation in ('missing', 'stale'):
                    saved = copy.deepcopy(self.manifest)
                    row = saved['admission']['stages'][stage]['empty_drops'][0]
                    if mutation == 'missing':
                        del row[key]
                    else:
                        row[key] = 'different-source'
                    with self.subTest(stage=stage, key=key, mutation=mutation):
                        with mock.patch.object(admission, 'inspect_stages', return_value=self.fresh):
                            with self.assertRaisesRegex(ValueError, 'proof records|admission evidence'):
                                admission.recheck(ROOT, self.work, saved)

    def test_changed_snapshot_is_rejected_before_inspection(self):
        for stage, filename in (('before', 'zerocopy.before.ullbc'), ('llbc', 'zerocopy.llbc')):
            path = self.work / filename
            original = path.read_bytes()
            path.write_bytes(original + b'\n')
            with self.subTest(stage=stage):
                with mock.patch.object(admission, 'inspect_stages') as inspect:
                    with self.assertRaisesRegex(ValueError, f'Stale {stage} admission snapshot'):
                        admission.recheck(ROOT, self.work, self.manifest)
                    inspect.assert_not_called()
            path.write_bytes(original)

    def test_missing_snapshot_hash_is_rejected_before_inspection(self):
        for stage in ('before', 'llbc'):
            saved = copy.deepcopy(self.manifest)
            del saved['admission']['stages'][stage]['sha256']
            with self.subTest(stage=stage):
                with mock.patch.object(admission, 'inspect_stages') as inspect:
                    with self.assertRaisesRegex(ValueError, f'Stale {stage} admission snapshot'):
                        admission.recheck(ROOT, self.work, saved)
                    inspect.assert_not_called()

    def test_recheck_compares_source_records_and_requests_bound_roots(self):
        # Fresh compilation can produce different artifact names or hashes.
        # Acceptance still requires equal body and snapshot source identities.
        for report in self.fresh.values():
            report['empty_drops'][0].update(proof_module='new_witness', proof_sha256='new-artifact')
        self.manifest['trait_laws'] = [{'rust': 'zerocopy::TestLaw'}]
        with mock.patch.object(admission, 'inspect_stages', return_value=self.fresh) as inspect:
            admission.recheck(ROOT, self.work, self.manifest)
        inspect.assert_called_once_with(ROOT, self.work, [ROOT_NAME], ['zerocopy::TestLaw'])


@unittest.skipUnless(LEAN.is_file(), 'requires installed pinned Lean')
class CompiledDropAdmissionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.scratch = tempfile.TemporaryDirectory(prefix='aeneas-drop-kernel-')
        cls.addClassCleanup(cls.scratch.cleanup)
        cls.driver = drop_ownership.KernelDrops(ROOT, Path(cls.scratch.name))
        # Build once, but use a distinct frozen stage for each independent case.
        # A present installation must pass production provenance validation.
        cls.driver.initialize()

    def certify(self, stage, function, contents=None):
        contents = snapshot_bytes(function) if contents is None else contents
        self.driver.freeze(stage, contents)
        return self.driver.certify(stage, function)

    def test_both_complete_body_stages_receive_fresh_kernel_proofs(self):
        for tag, stage in (('Unstructured', 'before'), ('Structured', 'final')):
            with self.subTest(stage=stage):
                function = function_fixture(tag)
                # An unused snapshot field still contributes to the identity.
                contents = snapshot_bytes(function, compiler_identity='test-fixture')
                record = self.certify(stage, function, contents)
                self.assertEqual(record['function_def_id'], FUNCTION_ID)
                self.assertEqual(record['body_sha256'],
                                 drop_ownership.body_digest(function['body']))
                self.assertEqual(record['snapshot_sha256'], hashlib.sha256(contents).hexdigest())
                self.assertEqual((self.driver.work / (stage + '.json')).read_bytes(), contents)
                proof = self.driver.work / (record['proof_module'] + '.olean')
                self.assertEqual(record['proof_sha256'], hashlib.sha256(proof.read_bytes()).hexdigest())

    def test_move_to_copy_mutation_fails_in_the_kernel(self):
        for tag in ('Unstructured', 'Structured'):
            stage = 'copy_' + tag.lower()
            with self.subTest(stage=tag):
                with self.assertRaisesRegex(ValueError, 'Kernel rejected empty-drop admission'):
                    self.certify(stage, function_fixture(tag, move='Copy'))
                self.assertNotIn((stage, FUNCTION_ID), self.driver.proofs)
                log = self.driver.work / f'DropWitness_{stage}_{FUNCTION_ID}.log'
                self.assertIn('(kernel) declaration type mismatch', log.read_text())

    def test_repaired_temporary_body_cannot_certify_the_original(self):
        # Lean can prove the repaired Move body. That proof must never be
        # recorded against the unsafe Copy body selected by Admission.
        stage = 'repaired_temporary_body'
        original = function_fixture(move='Copy')
        repaired = snapshot_bytes(function_fixture())
        run = self.driver.run

        def repair_then_check(module, env=None):
            (self.driver.work / (stage + '.json')).write_bytes(repaired)
            return run(module, env)

        with mock.patch.object(self.driver, 'run', side_effect=repair_then_check):
            with self.assertRaisesRegex(ValueError, 'inputs changed during kernel checking'):
                self.certify(stage, original)
        self.assertNotIn((stage, FUNCTION_ID), self.driver.proofs)

    def test_edited_witness_cannot_omit_the_kernel_command(self):
        stage = 'edited_witness'
        run = self.driver.run

        def erase_then_check(module, env=None):
            (self.driver.work / (module + '.lean')).write_text('import DropAudit\n')
            return run(module, env)

        with mock.patch.object(self.driver, 'run', side_effect=erase_then_check):
            with self.assertRaisesRegex(ValueError, 'inputs changed during kernel checking'):
                self.certify(stage, function_fixture(move='Copy'))
        self.assertNotIn((stage, FUNCTION_ID), self.driver.proofs)

    def test_unknown_executable_field_cannot_receive_a_proof(self):
        function = function_fixture()
        function['body']['Unstructured']['body'][0]['statements'][0]['hidden_move'] = 1
        with self.assertRaisesRegex(ValueError, 'Kernel rejected empty-drop admission'):
            self.certify('unknown_field', function)
        self.assertNotIn(('unknown_field', FUNCTION_ID), self.driver.proofs)

    def test_changing_frozen_snapshot_bytes_cannot_reuse_a_proof(self):
        function = function_fixture()
        original = snapshot_bytes(function)
        first = self.certify('changed_buffer', function, original)
        changed = original + b'\n'
        self.assertEqual(json.loads(original), json.loads(changed))
        self.driver.freeze('changed_buffer', changed)
        with self.assertRaisesRegex(ValueError, 'Frozen drop-admission snapshot changed'):
            self.driver.certify('changed_buffer', function)
        self.assertEqual((self.driver.work / 'changed_buffer.json').read_bytes(), original)
        self.assertNotEqual(first['snapshot_sha256'], hashlib.sha256(changed).hexdigest())

    def test_tampered_snapshot_file_is_rejected(self):
        function = function_fixture()
        original = snapshot_bytes(function)
        self.certify('changed_file', function, original)
        (self.driver.work / 'changed_file.json').write_bytes(original + b'\n')
        with self.assertRaisesRegex(ValueError, 'Frozen drop-admission snapshot changed'):
            self.driver.certify('changed_file', function)

    def test_lean_command_independently_rejects_duplicate_native_ids(self):
        function = function_fixture()
        snapshot = self.driver.work / 'duplicate_command.json'
        snapshot.write_text(json.dumps({'has_errors': False, 'translated': {
            'fun_decls': [function, copy.deepcopy(function)]}}))
        module = 'DuplicateNativeDropControl'
        (self.driver.work / (module + '.lean')).write_text(
            f'import DropAudit\ncertify_empty_drops {FUNCTION_ID}\n')
        env = dict(self.driver.env, AENEAS_DROP_SNAPSHOT=str(snapshot))
        with self.assertRaisesRegex(ValueError, 'Missing or ambiguous native function'):
            self.driver.run(module, env)

    def test_admission_uses_kernel_certificates_for_both_stages(self):
        for tag in ('Unstructured', 'Structured'):
            data, function = admission_fixture(tag)
            stage = 'audit_' + tag.lower()
            self.driver.freeze(stage, json.dumps(data).encode())
            with self.subTest(stage=tag):
                report = admission.Admission(data, [], certify_drops=
                    lambda current, stage=stage: self.driver.certify(stage, current)).audit([ROOT_NAME])
                self.assertEqual(report['roots'], [ROOT_NAME])
                self.assertEqual(report['empty_drops'], [self.driver.proofs[stage, FUNCTION_ID]])
                self.assertEqual(report['executions'], [{'rust': ROOT_NAME, 'origin': 'body'}])
                self.assertEqual(report['empty_drops'][0]['body_sha256'],
                                 drop_ownership.body_digest(function['body']))

    def test_recheck_rebuilds_checker_and_kernel_witnesses_for_both_stages(self):
        with tempfile.TemporaryDirectory(prefix='aeneas-fresh-drop-recheck-') as directory:
            work = Path(directory)
            manifest = recheck_fixture(work)
            saved = admission.inspect_stages(ROOT, work, [ROOT_NAME], [])
            manifest['admission']['stages'] = copy.deepcopy(saved)
            previous_builds = set(work.glob('empty-drops-*'))
            self.assertEqual(len(previous_builds), 1)
            # Saved compiled-witness fields are deliberately unusable. A fresh
            # proof must establish the same complete-body source identities.
            for report in manifest['admission']['stages'].values():
                report['empty_drops'][0].update(proof_module='absent_saved_witness',
                                              proof_sha256='untrusted-saved-artifact')
            real_run = drop_ownership.KernelDrops.run
            runs = []

            def record_run(driver, module, env=None):
                runs.append((driver.work, module))
                return real_run(driver, module, env)

            with mock.patch.object(drop_ownership.KernelDrops, 'run', new=record_run):
                admission.recheck(ROOT, work, manifest)
            self.assertEqual([module for _, module in runs], [
                'DropOwnership', 'DropJson', 'DropAudit',
                f'DropWitness_before_{FUNCTION_ID}', f'DropWitness_llbc_{FUNCTION_ID}'])
            self.assertTrue(all(directory not in previous_builds for directory, _ in runs))


if __name__ == '__main__':
    unittest.main()
