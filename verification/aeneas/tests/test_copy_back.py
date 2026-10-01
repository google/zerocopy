# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import contextlib
import copy
import io
import json
import shutil
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import copy_back
import inline
import workspace
from test_inline import BLOCK, ENTRY, GENERATED, ROOT, RUST, fixture

TYPE = 'zerocopy::util::Box'
MODEL = '/// ```aeneas\n/// model BoxValue := Fields\n/// decode self => self\n/// ```\n'
TYPES = ('module\nnamespace Zerocopy\n/-- [zerocopy::util::Box]\n Source: x -/\n'
         'structure util.Box (T : Type) where\n  val : T\n\nend Zerocopy\n')


class CopyBackTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.work = self.root / 'work'
        self.source = self.root / ENTRY['file']

    def generate(self, source=None, second=False, model=False):
        if source is None:
            source = (MODEL + 'struct Box<T>(T);\n' if model else '') + BLOCK + 'fn f(x: usize) {}\n'
            if second:
                source += BLOCK.replace('f_spec', 'g_spec') + 'fn g(x: usize) {}\n'
        annotations = fixture(self.root, source)
        (self.work / 'Zerocopy').mkdir(parents=True, exist_ok=True)
        generated = GENERATED
        if second:
            generated = generated.replace('\nend Zerocopy', '\n' + GENERATED.split('namespace Zerocopy\n')[1].replace(
                'zerocopy::util::f', 'zerocopy::util::g').replace('util.f', 'util.g').split('\nend Zerocopy')[0] + '\nend Zerocopy')
        (self.work / 'Zerocopy/Funs.lean').write_text(generated)
        if model:
            (self.work / 'Zerocopy/Types.lean').write_text(TYPES)
        lean = self.root / 'verification/aeneas/lean'
        lean.mkdir(parents=True, exist_ok=True)
        (lean / 'RequiredContracts.lean').write_text('')
        inline.save_bindings(self.root, annotations, self.work, development=True)
        inline.assemble(self.root, annotations, self.work, development=True)
        return annotations

    def edit(self, module, old, new):
        path = self.work / f'{module}.lean'
        text = path.read_text()
        self.assertIn(old, text)
        path.write_text(text.replace(old, new, 1))

    def files(self):
        return {str(p.relative_to(self.root)): p.read_bytes() for p in self.root.rglob('*') if p.is_file()}

    def run_copy(self, owner=RUST, apply=False, **kwargs):
        with contextlib.redirect_stdout(io.StringIO()) as output:
            diff = copy_back.copy_back(self.root, self.work, owner, apply=apply, **kwargs)
        return diff, output.getvalue()

    def fails_without_writes(self, owner=RUST, message=None):
        before = self.files()
        with self.assertRaisesRegex(ValueError, message or '.'):
            self.run_copy(owner, apply=True)
        self.assertEqual(before, self.files())

    def test_spec_line_count_preview_apply_and_native_regeneration_round_trip(self):
        self.generate()
        self.edit('Specs', '  ensures r => r = x', '  requires positive : x > 0\n  ensures r =>\n    r = x + 1')
        edited = (self.work / 'Specs.lean').read_bytes()
        before = self.files()
        diff, printed = self.run_copy()
        self.assertEqual(diff, printed)
        self.assertIn('+///   requires positive : x > 0', diff)
        self.assertEqual(before, self.files())
        self.run_copy(apply=True)
        self.assertIn(b'///     r = x + 1\n', self.source.read_bytes())
        workspace.protect_projections(self.work)
        self.generate(self.source.read_bytes().decode())
        self.assertEqual(edited, (self.work / 'Specs.lean').read_bytes())

    def test_shape_and_decoder_are_one_annotation_and_leave_other_owner_dirty(self):
        self.generate(model=True)
        self.edit('ModelShapes', 'model BoxValue := Fields', 'model BoxValue where\n  val : T\n  extra : Nat')
        self.edit('Models', 'decode self =>\n  self', 'decode? self =>\n  some { val := self.val, extra := 0 }')
        self.edit('Specs', 'r = x', 'r ≠ x')
        specs = (self.work / 'Specs.lean').read_bytes()
        before = self.source.read_bytes()
        self.run_copy(TYPE, apply=True)
        source = self.source.read_bytes()
        self.assertTrue(source.endswith(before[before.index(BLOCK.encode()):]))
        self.assertIn(b'///   extra : Nat\n/// decode? self =>', source)
        self.assertEqual(specs, (self.work / 'Specs.lean').read_bytes())
        with self.assertRaisesRegex(ValueError, 'Refusing to overwrite'):
            workspace.protect_projections(self.work)
        self.run_copy(apply=True)
        workspace.protect_projections(self.work)
        edited = {m: (self.work / f'{m}.lean').read_bytes() for m in workspace.PROJECTIONS}
        self.generate(self.source.read_bytes().decode(), model=True)
        self.assertEqual(edited, {m: (self.work / f'{m}.lean').read_bytes() for m in workspace.PROJECTIONS})

    def test_unicode_crlf_indented_docs_and_mode_preserve_every_other_byte(self):
        source = '// 雪 documentation\n' + ''.join('    ' + line for line in BLOCK.splitlines(keepends=True)) + '    fn f(x: usize) {}\n'
        source = source.replace('\n', '\r\n')
        annotations = self.generate(source)
        span = annotations[RUST]['copy_span']
        self.source.chmod(0o640)
        before = self.source.read_bytes()
        self.edit('Specs', 'r = x', 'r ≠ x\n    -- 雪')
        self.run_copy(apply=True)
        after = self.source.read_bytes()
        self.assertEqual(after[:span['start']], before[:span['start']])
        self.assertTrue(after.endswith(before[span['end']:]))
        self.assertIn('    ///     -- 雪\r\n'.encode(), after)
        self.assertNotIn(b'\n', after.replace(b'\r\n', b''))
        self.assertEqual(stat.S_IMODE(self.source.stat().st_mode), 0o640)

    def test_two_function_owners_shift_spans_without_adopting_other_edits(self):
        self.generate(second=True)
        self.edit('Specs', 'r = x', 'r ≠ x\n    ∧ True')
        self.edit('Specs', 'spec g_spec\n  for @Zerocopy.util.g with 0 type parameters\n  ensures r => r = x',
                  'spec g_spec\n  for @Zerocopy.util.g with 0 type parameters\n  ensures r => r = x + 2')
        lean = (self.work / 'Specs.lean').read_bytes()
        self.run_copy(apply=True)
        self.assertIn(b'///   ensures r => r = x\n', self.source.read_bytes())
        self.assertEqual(lean, (self.work / 'Specs.lean').read_bytes())
        with self.assertRaisesRegex(ValueError, 'Refusing to overwrite'):
            workspace.protect_projections(self.work)
        self.run_copy('zerocopy::util::g', apply=True)
        workspace.protect_projections(self.work)
        self.assertIn(b'r = x + 2', self.source.read_bytes())

    def test_generated_application_import_check_and_derive_edits_rejected(self):
        changes = [('Specs', '  for @Zerocopy.util.f', '  for @Zerocopy.util.g'),
                   ('Specs', 'public import Models', 'public import Other'),
                   ('Specs', 'check_model_inputs', 'check_other_inputs'),
                   ('Specs', 'check_spec_binding', 'check_other_binding'),
                   ('ModelShapes', 'type parameters begin', 'type parameters begin\n-- scratch'),
                   ('Models', 'derive_rust_model Zerocopy.util.Box', 'derive_rust_model Zerocopy.util.Other'),
                   ('Models', 'check_model_binding', 'check_other_binding')]
        self.generate(model=True)
        baseline = self.files()
        for module, old, new in changes:
            with self.subTest(module=module, old=old):
                self.edit(module, old, new)
                self.fails_without_writes(TYPE if module != 'Specs' else RUST)
                for relative, contents in baseline.items():
                    (self.root / relative).write_bytes(contents)

    def test_moving_generated_for_target_is_rejected_without_writes(self):
        self.generate()
        application = '  for @Zerocopy.util.f with 0 type parameters'
        self.edit('Specs', application + '\n  ensures r => r = x',
                  '  ensures r => r = x\n' + application)
        self.fails_without_writes(message='immediately before the first specification clause')

    def test_added_binder_lines_move_canonical_for_target_and_round_trip(self):
        self.generate()
        application = '  for @Zerocopy.util.f with 0 type parameters'
        self.edit('Specs', 'spec f_spec\n' + application,
                  'spec f_spec\n  (ghost : Nat)\n' + application)
        projected = (self.work / 'Specs.lean').read_bytes()
        self.run_copy(apply=True)
        self.assertIn(b'/// spec f_spec\n///   (ghost : Nat)\n///   ensures', self.source.read_bytes())
        workspace.protect_projections(self.work)
        self.generate(self.source.read_bytes().decode())
        self.assertEqual(projected, (self.work / 'Specs.lean').read_bytes())

    def test_specification_trailing_blank_edit_is_rejected_without_poisoning_regeneration(self):
        self.generate()
        original = (self.work / 'Specs.lean').read_bytes()
        self.edit('Specs', '  ensures r => r = x\n-- aeneas-copy-end',
                  '  ensures r => r = x\n\n-- aeneas-copy-end')
        self.fails_without_writes(message='remove trailing blank lines')
        (self.work / 'Specs.lean').write_bytes(original)
        self.generate(self.source.read_bytes().decode())
        self.assertEqual(original, (self.work / 'Specs.lean').read_bytes())

    def test_inline_decoder_edit_is_rejected_with_normalization_advice(self):
        self.generate(model=True)
        self.edit('Models', 'decode self =>\n  self', 'decode self => self')
        self.fails_without_writes(TYPE, message='body on separate lines indented by two spaces')

    def test_original_rust_spec_trailing_blanks_remain_readable_and_noop_preserved(self):
        source = BLOCK.replace('/// ```\n', '/// \n/// \n/// ```\n') + 'fn f(x: usize) {}\n'
        self.generate(source)
        before = self.files()
        self.run_copy(apply=True)
        self.assertEqual(before, self.files())
        self.generate(source)
        self.assertEqual(self.source.read_bytes(), source.encode())
        workspace.protect_projections(self.work)

    def test_model_trailing_blank_edits_are_rejected_before_writes(self):
        self.generate(model=True)
        for module in ('ModelShapes', 'Models'):
            with self.subTest(module=module):
                original = (self.work / f'{module}.lean').read_bytes()
                self.edit(module, '\n-- aeneas-copy-end', '\n\n-- aeneas-copy-end')
                self.fails_without_writes(TYPE, message='remove trailing blank lines')
                (self.work / f'{module}.lean').write_bytes(original)

    def test_nested_fake_duplicate_and_missing_markers_rejected(self):
        self.generate()
        original = (self.work / 'Specs.lean').read_bytes()
        begin = f'-- aeneas-copy-begin {RUST} spec\n'
        end = f'-- aeneas-copy-end {RUST} spec\n'
        for change in (begin + begin, '-- aeneas-copy-begin fake spec\n', '-- aeneas-copy-begin ' + RUST + ' shape\n', ''):
            with self.subTest(change=change):
                (self.work / 'Specs.lean').write_bytes(original.replace(begin.encode(), change.encode()))
                self.fails_without_writes()
        (self.work / 'Specs.lean').write_bytes(original + begin.encode() + end.encode())
        self.fails_without_writes()

    def test_unsupported_doc_forms_keep_read_support_and_fail_copy(self):
        for source in ('/**\n```aeneas\nspec f_spec\n  ensures r => r = x\n```\n*/\nfn f(x: usize) {}\n',
                       '#[doc = "```aeneas\\nspec f_spec\\n  ensures r => r = x\\n```"]\nfn f(x: usize) {}\n'):
            with self.subTest(source=source):
                self.generate(source)
                self.fails_without_writes(message='other doc forms are read-only')

    def test_stale_rust_and_malformed_metadata_have_no_writes(self):
        self.generate()
        self.edit('Specs', 'r = x', 'r ≠ x')
        original = self.source.read_bytes()
        self.source.write_bytes(original + b'// independent Rust edit\n')
        self.fails_without_writes(message='Rust source changed')
        self.source.write_bytes(original)
        path = self.work / workspace.PROJECTION_STATE
        state = json.loads(path.read_bytes())
        variants = [[], {'version': 1}, {**state, 'version': 3}, {**state, 'projections': {}}, {**state, 'sources': {}}]
        wrong_span = copy.deepcopy(state)
        wrong_span['owners'][RUST]['copy_span']['start'] += 1
        variants.append(wrong_span)
        missing_owner = copy.deepcopy(state)
        missing_owner['owners'][RUST]['file'] = '../escape.rs'
        variants.append(missing_owner)
        for variant in variants:
            with self.subTest(variant=variant):
                path.write_text(json.dumps(variant))
                self.fails_without_writes()
        path.write_text('{')
        self.fails_without_writes(message='Malformed')

    def test_interruption_after_rust_write_recovers_then_retries_idempotently(self):
        self.generate()
        self.edit('Specs', 'r = x', 'r ≠ x\n    ∧ True')
        control = (self.work / workspace.PROJECTION_STATE).read_bytes()
        projections = {m: (self.work / f'{m}.lean').read_bytes() for m in workspace.PROJECTIONS}
        with self.assertRaisesRegex(RuntimeError, 'interrupted'):
            self.run_copy(apply=True, after_source_write=lambda: (_ for _ in ()).throw(RuntimeError('interrupted')))
        self.assertIn('r ≠ x'.encode(), self.source.read_bytes())
        self.assertEqual(control, (self.work / workspace.PROJECTION_STATE).read_bytes())
        self.assertEqual(projections, {m: (self.work / f'{m}.lean').read_bytes() for m in workspace.PROJECTIONS})
        self.run_copy(apply=True)
        workspace.protect_projections(self.work)
        before = self.files()
        self.run_copy(apply=True)
        self.assertEqual(before, self.files())

    def test_symlink_files_and_parent_directories_rejected(self):
        self.generate()
        self.edit('Specs', 'r = x', 'r ≠ x')
        for target in (self.source, self.work / 'Specs.lean', self.work / workspace.PROJECTION_STATE):
            with self.subTest(target=target):
                moved = target.with_name(target.name + '.real')
                target.rename(moved)
                target.symlink_to(moved)
                self.fails_without_writes(message='symlink')
                target.unlink()
                moved.rename(target)
        parent = self.source.parent
        moved = parent.with_name('real-util')
        parent.rename(moved)
        parent.symlink_to(moved, target_is_directory=True)
        self.fails_without_writes(message='symlink')

    def test_source_maps_are_diagnostic_only_and_cannot_redirect_an_edit(self):
        self.generate()
        self.edit('Specs', 'r = x', 'r ≠ x')
        unrelated = self.root / 'zerocopy/src/unrelated.rs'
        unrelated.write_text('unique unrelated Rust source\n')
        for module in workspace.PROJECTIONS:
            (self.work / f'{module}.source-map.json').write_text(json.dumps({
                '1': {'file': 'zerocopy/src/unrelated.rs', 'line': 1}}))
        self.run_copy(apply=True)
        self.assertIn('r ≠ x'.encode(), self.source.read_bytes())
        self.assertEqual(unrelated.read_text(), 'unique unrelated Rust source\n')

    def test_malformed_authored_payload_is_rejected_before_writes(self):
        self.generate(model=True)
        originals = {module: (self.work / f'{module}.lean').read_bytes() for module in workspace.PROJECTIONS}
        for module, old, new, owner in [
                ('Specs', '  ensures r => r = x', '  theorem bad : True := by trivial', RUST),
                ('Specs', '  ensures r => r = x', '  ensures r = x', RUST),
                ('Models', 'decode self =>\n  self', 'decode self =>\n  self\ndecode other => other', TYPE),
                ('ModelShapes', 'model BoxValue := Fields', 'model Fields := Fields', TYPE)]:
            with self.subTest(module=module, new=new):
                self.edit(module, old, new)
                self.fails_without_writes(owner)
                (self.work / f'{module}.lean').write_bytes(originals[module])

    def test_noop_has_no_writes_even_for_inline_decoder_spelling(self):
        self.generate(model=True)
        before = self.files()
        self.run_copy(TYPE, apply=True)
        self.run_copy(apply=True)
        self.assertEqual(before, self.files())

    def test_input_changes_immediately_before_replace_abort_without_rust_write(self):
        self.generate()
        self.edit('Specs', 'r = x', 'r ≠ x')
        source = self.source.read_bytes()
        original_replace = copy_back.replace

        def raced(record, contents, guard):
            (self.work / 'Specs.lean').write_text('changed during planning')
            return original_replace(record, contents, guard)

        with mock.patch.object(copy_back, 'replace', side_effect=raced), self.assertRaisesRegex(ValueError, 'input changed'):
            self.run_copy(apply=True)
        self.assertEqual(source, self.source.read_bytes())
        self.assertFalse(list(self.source.parent.glob('.aeneas-copy-*')))

    def test_v1_protection_and_clean_regeneration_upgrade(self):
        self.generate()
        workspace.record_projections(self.work)
        workspace.protect_projections(self.work)
        self.fails_without_writes(message='version 2')
        self.generate(self.source.read_bytes().decode())
        self.assertEqual(json.loads((self.work / workspace.PROJECTION_STATE).read_bytes())['version'], 2)
        self.run_copy(apply=True)

    def test_real_dev_script_previews_and_applies_with_system_bash(self):
        self.generate()
        self.edit('Specs', 'r = x', 'r ≠ x')
        project = self.root / 'verification/aeneas/lean'
        shutil.copytree(self.work, project, dirs_exist_ok=True)
        scripts = project.parent
        for name in ('dev.sh', 'workspace.py', 'copy_back.py', 'inline.py', 'golden.py'):
            shutil.copyfile(ROOT / 'verification/aeneas' / name, scripts / name)
        # No toolchain or extraction driver is supplied: both routes must read
        # this existing project directly, even with macOS's system Bash 3.2.
        command = ['/bin/bash', str(scripts / 'dev.sh'), '--copy-back', RUST]
        before = self.files()
        preview = subprocess.run([*command, '--dry-run'], capture_output=True, text=True)
        self.assertEqual(preview.returncode, 0, preview.stderr)
        self.assertIn('+///   ensures r => r ≠ x', preview.stdout)
        self.assertEqual(before, self.files())
        applied = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(applied.returncode, 0, applied.stderr)
        self.assertEqual(preview.stdout, applied.stdout)
        after = self.files()
        self.assertEqual({name for name in before if before[name] != after[name]},
                         {ENTRY['file'], 'verification/aeneas/lean/' + workspace.PROJECTION_STATE})
        self.assertIn('r ≠ x'.encode(), self.source.read_bytes())
        workspace.protect_projections(project)

    def test_cli_preview_and_incompatible_dev_flags(self):
        self.generate()
        self.edit('Specs', 'r = x', 'r ≠ x')
        before = self.files()
        result = subprocess.run([sys.executable, '-B', str(ROOT / 'verification/aeneas/workspace.py'),
                                 'copy-back', str(self.work), '--root', str(self.root), '--owner', RUST],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('+///   ensures r => r ≠ x', result.stdout)
        self.assertEqual(before, self.files())
        for extra in ('--live', '--check'):
            result = subprocess.run(['bash', str(ROOT / 'verification/aeneas/dev.sh'), '--copy-back', RUST, extra],
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('cannot be combined', result.stderr)


if __name__ == '__main__':
    unittest.main()
