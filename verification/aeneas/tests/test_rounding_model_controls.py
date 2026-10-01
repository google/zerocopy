# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Bounded fixtures for production rounding control selection and diagnostics."""
import json
import os
from pathlib import Path
import tempfile
import unittest

import rounding_model_controls as controls


class RoundingControlTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.old_cwd = Path.cwd()
        os.chdir(self.temp.name)
        self.addCleanup(self.restore_directory)
        for module, theorem in controls.PROBES.values():
            Path(module + '.lean').write_text(
                'namespace Zerocopy\n\ntheorem ' + theorem + ' : True := by\n'
                '  trivial\n\ntheorem next_law : True := by trivial\n')
        Path('ModelShapes.lean').write_text('')
        Path('SpecsSyntax.lean').write_text('')
        Path('Zerocopy').mkdir()
        Path('Zerocopy/Funs.lean').write_text('')
        self.spec = ('spec encoding_new_spec\n  for @' + controls.OWNER + '.new with 0 type parameters\n'
                     '  ensures encoded => encoded.align = (align : Nat) ∧ encoded.phase = (phase : Nat)\n')
        Path('Specs.lean').write_text('aeneas_spec_begin\n' + self.spec + 'aeneas_spec_end\n')
        self.models = ('-- preceding sibling\n' + controls.PREFIX + ' decode self =>\n'
                       '  { align := 2, phase := 1, .. }\n'
                       'check_model_binding ' + controls.OWNER + ' with 0 type parameters\n'
                       '-- following sibling and local tuple provider\n')
        Path('Models.lean').write_text(self.models)
        self.manifest = {'version': 3, 'mode': 'verified-live', 'bindings': {
            'zerocopy::layout::RoundingAlignAndPhase': {
                'kind': 'type', 'raw': controls.OWNER,
                'model': controls.OWNER + '.RoundingValue'}}}
        self.write_manifest()

    def restore_directory(self):
        os.chdir(self.old_cwd)
        self.temp.cleanup()

    def write_manifest(self):
        Path('bindings.json').write_text(json.dumps(self.manifest))

    def check_log(self, text, kind='none'):
        Path('failure.log').write_text(text)
        controls.check_failure(kind, 'failure.log')

    def test_native_renderer_and_lake_renderer(self):
        # These are the real renderer prefixes; locations are adjusted to this
        # compact fixture's operation-promise or domain span.
        fixtures = [
            ('none', '/probe/generated/RoundingDomainControl.lean:3:41: error: unsolved goals\n'
             'case pos\nhp : 0 < code._0.val.val\n⊢ False\n'),
            ('none', '✖ [2/2] Building RoundingDomainControl\n'
             'error: generated/RoundingDomainControl.lean:3:41: unsolved goals\n'
             'case pos\nhp : 0 < code._0.val.val\n⊢ False\n'
             'error: Lean exited with code 1\nerror: build failed\n'),
            ('constant', '/probe/generated/RoundingConstructorControl.lean:3:14: error: '
             'Application type mismatch: The argument\n  rfl\n'),
            ('constant', 'error: generated/RoundingConstructorControl.lean:3:14: '
             'Application type mismatch: The argument\n  rfl\n'
             'error: Lean exited with code 1\nerror: build failed\n'),
        ]
        for kind, text in fixtures:
            with self.subTest(kind=kind, text=text):
                self.check_log(text, kind)

    def test_mixed_semantic_and_unrelated_errors_fail_closed(self):
        semantic = 'error: RoundingDomainControl.lean:3:41: unsolved goals\n⊢ False\n'
        unrelated = [
            "error: RoundingDomainControl.lean:9:1: (kernel) unknown constant '_private.Models.0._proof_3'\n",
            "Other.lean:1:1: error: Unknown identifier `missing`\n",
            "error: Other.lean:1:1: object file 'Missing.olean' of module Missing does not exist\n",
            'error: cannot locate module Missing\n',
            'wrapper error: unrecognized kernel failure\n',
            'Other.lean:3:1: error: unsolved goals\n',
            'RoundingDomainControl.lean:1:1: error: unsolved goals\n',
        ]
        for suffix in unrelated:
            with self.subTest(suffix=suffix), self.assertRaises(ValueError):
                self.check_log(semantic + suffix)

    def test_wrong_probe_or_missing_diagnostic_does_not_count(self):
        for text in ['error: Other.lean:3:41: unsolved goals\n',
                     'error: RoundingDomainControl.lean:6:41: unsolved goals\n',
                     'error: Lean exited with code 1\nerror: build failed\n']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                self.check_log(text)

    def test_selected_capability_and_lost_owner(self):
        self.assertTrue(controls.capability())
        for field, value in [('kind', 'function'), ('model', controls.OWNER + '.Forgetful'),
                             ('raw', 'OtherRaw')]:
            owner = self.manifest['bindings']['zerocopy::layout::RoundingAlignAndPhase']
            old = owner[field]
            owner[field] = value
            self.write_manifest()
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'lost'):
                controls.capability()
            owner[field] = old
        self.manifest['bindings'].clear()
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, 'lost'):
            controls.capability()
        Path('Models.lean').write_text('')
        self.assertFalse(controls.capability())

    def test_selected_capability_requires_operation_modules(self):
        Path('Specs.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'prerequisite: Specs'):
            controls.capability()

    def test_probes_reuse_constructor_fence_and_independent_input(self):
        for module, _ in controls.PROBES.values():
            Path(module + '.lean').unlink()
        controls.write_probes()
        constructor = Path('RoundingConstructorControl.lean').read_text()
        domain = Path('RoundingDomainControl.lean').read_text()
        self.assertIn(self.spec, constructor)
        self.assertIn('encoding_new_spec_contract align phase (.ok code)', constructor)
        self.assertIn('constructor_result', constructor)
        self.assertIn('isValid code', domain)
        for source in (constructor, domain):
            self.assertNotIn('import MathViews', source)
            self.assertNotIn('import RepresentationLaws', source)
            self.assertNotIn('derive_rust_model', source)
        with self.assertRaisesRegex(ValueError, 'already exists'):
            controls.write_probes()

    def test_constructor_fence_selection_fails_closed(self):
        original = Path('Specs.lean').read_text()
        for source in (original + original, original.replace('encoding_new_spec', 'other_spec'),
                       original.replace(controls.OWNER + '.new', 'Other.new')):
            Path('Specs.lean').write_text(source)
            with self.subTest(source=source), self.assertRaises(ValueError):
                controls.constructor_spec()

    def test_mutations_touch_only_selected_decoder(self):
        marker = 'check_model_binding ' + controls.OWNER
        prefix, suffix = self.models.split(controls.PREFIX)[0], self.models[self.models.index(marker):]
        for kind, body in [('constant', controls.CONSTANT), ('none', controls.REJECT)]:
            Path('Models.lean').write_text(self.models)
            controls.mutate(kind)
            self.assertEqual(Path('Models.lean').read_text(), prefix + body + suffix)

    def test_bad_mutation_boundaries_leave_source_unchanged(self):
        marker = 'check_model_binding ' + controls.OWNER + ' with 0 type parameters\n'
        fixtures = [self.models + controls.PREFIX,
                    self.models.replace(marker, ''),
                    marker + self.models.replace(marker, ''),
                    self.models.replace(marker, 'derive_rust_model Another with 0 type parameters\n' + marker),
                    self.models.replace(marker, 'check_model_binding Another with 0 type parameters\n' + marker),
                    self.models.replace(marker, 'def unrelated := 0\n' + marker)]
        for source in fixtures:
            Path('Models.lean').write_text(source)
            with self.subTest(source=source), self.assertRaises(ValueError):
                controls.mutate('none')
            self.assertEqual(Path('Models.lean').read_text(), source)
        Path('Models.lean').write_text(self.models)
        with self.assertRaises(ValueError):
            controls.mutate('invalid')
        self.assertEqual(Path('Models.lean').read_text(), self.models)


if __name__ == '__main__':
    unittest.main()
