# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import json
import copy
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'verification/aeneas'))
import inline

TOOL = ROOT / 'target/aeneas/annotation-tool/debug/aeneas-inline'
BLOCK = ('    // ```aeneas\n'
         '    // model:\n'
         '    //   def util.f (x : Nat) :=\n'
         '    //     x\n'
         '    // proof:\n'
         '    //   theorem f_spec : True := by\n'
         '    //     trivial\n'
         '    // ```\n')
ENTRY = {'rust': 'zerocopy::util::f', 'file': 'zerocopy/src/util/mod.rs',
         'syntax': 'f', 'model': 'util.f', 'theorem': 'f_spec', 'golden': 'util.f.lean.in'}


def syntax(source):
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / 'source.rs'
        path.write_bytes(source.encode())
        result = subprocess.run([str(TOOL)], input=json.dumps([str(path)]),
                                text=True, capture_output=True)
        if result.returncode:
            raise ValueError(result.stderr)
        return json.loads(result.stdout)[str(path)]


class InlineTests(unittest.TestCase):
    def parse(self, source):
        return inline.parse_file(source, syntax(source))

    def test_first_token_and_indentation_with_crlf_unicode_and_inactive_cfg(self):
        for eol in ('\n', '\r\n'):
            source = ('const 雪: u8 = 0;\n#[cfg(any())]\nfn f() {\n\n' + BLOCK + '}').replace('\n', eol)
            found = self.parse(source)
            self.assertEqual(len(found), 1)
            self.assertEqual(found[0]['syntax'], 'f')
            self.assertEqual(found[0]['model_text'], 'def util.f (x : Nat) :=\n  x\n')
            self.assertEqual(found[0]['newline'], eol)
            self.assertIn('proof:', source[found[0]['model_end']:])

    def test_rejects_comments_statements_and_nested_scopes_before_fence(self):
        for before in ('// preceding comment\n', '/* preceding */', 'let x = 1;\n',
                       '#[allow(unused)] let x = 1;\n', '{\n'):
            extra_end = '}' if before == '{\n' else ''
            with self.subTest(before=before), self.assertRaises(ValueError):
                self.parse('fn f() {\n' + before + BLOCK + extra_end + '}')
        for source in (BLOCK + 'fn f() {}',
                       'fn outer() { fn f() {\n' + BLOCK + '} }',
                       'impl S { fn f() {\n' + BLOCK + '} }'):
            with self.assertRaises(ValueError):
                self.parse(source)

    def test_rejects_near_miss_guards_missing_sections_and_broken_fences(self):
        variants = [BLOCK.replace('```aeneas', '```Aeneas'),
                    BLOCK.replace('```aeneas', '```aeneos'),
                    BLOCK.replace('```aeneas', '``aeneas'),
                    BLOCK.replace('```aeneas', '```aeneas v2'),
                    BLOCK.replace('// ```aeneas', '/// ```aeneas'),
                    BLOCK.replace('// proof:', '// proofs:'),
                    BLOCK.replace('// model:', '// proof:'),
                    BLOCK.replace('//   def', '// def'),
                    BLOCK.replace('    // ```\n', ''),
                    BLOCK.replace('    // ```\n', '    // ``` trailing\n'),
                    BLOCK.replace('    // proof:', '    let x = 1;\n    // proof:'),
                    BLOCK.replace('    // proof:', '    //   def extra := 1\n    // proof:')]
        for block in variants:
            with self.subTest(block=block), self.assertRaises(ValueError):
                self.parse('fn f() {\n' + block + '}')

    def test_fake_fences_in_literals_are_not_annotations(self):
        source = 'fn f() { let x = r###"\n' + BLOCK + '"###; }'
        self.assertEqual(self.parse(source), [])
        with self.assertRaises(ValueError):
            self.parse('fn f() { /* ```aeneas\nmodel:\nproof:\n``` */ }')

    def test_discovery_registration_and_golden_bijection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / ENTRY['file']
            source.parent.mkdir(parents=True)
            source.write_text('fn f() {\n' + BLOCK + '}')
            entries = [ENTRY]
            self.assertEqual(set(inline.discover(root, TOOL, entries)), {ENTRY['rust']})
            directory = root / 'verification/aeneas/golden'
            directory.mkdir(parents=True)
            with self.assertRaises(ValueError):
                inline.templates(root, entries)
            inline.templates(root, entries, allow_missing=True)
            golden = directory / ENTRY['golden']
            golden.write_text(f'@@AENEAS_MODEL("{ENTRY["rust"]}")@@\n')
            inline.templates(root, entries)
            extra = directory / 'orphan.lean.in'
            extra.write_text('orphan')
            with self.assertRaises(ValueError):
                inline.templates(root, entries)
            extra.unlink()
            golden.write_text('@@AENEAS_MODEL("wrong")@@\n')
            with self.assertRaises(ValueError):
                inline.templates(root, entries)
            source.write_text('fn f() {}')
            with self.assertRaises(ValueError):
                inline.discover(root, TOOL, entries)
            source.write_text(('fn f() {\n' + BLOCK + '}\n') * 2)
            with self.assertRaises(ValueError):
                inline.discover(root, TOOL, entries)
            source.write_text('fn f() {\n' + BLOCK + '}')
            outside = root / 'unregistered.rs'
            outside.write_text('fn other() {\n' + BLOCK + '}')
            with self.assertRaises(ValueError):
                inline.discover(root, TOOL, entries)
            outside.unlink()
            source.write_text('fn wrong() {\n' + BLOCK + '}')
            with self.assertRaises(ValueError):
                inline.discover(root, TOOL, entries)

    def test_generated_split_and_model_updates_preserve_proof_and_rust(self):
        generated = ('module\nnamespace Zerocopy\n'
                     '/-- [zerocopy::util::f]:\n    Source: location -/\n'
                     'def util.f (x : Nat) :=\n  x + 1\n\nend Zerocopy\n')
        models, scaffold = inline.split_live(generated, [ENTRY])
        self.assertEqual(models[ENTRY['rust']], 'def util.f (x : Nat) :=\n  x + 1\n')
        self.assertIn('@@AENEAS_GOLDEN("util.f.lean.in")@@', scaffold)
        for bad in (generated.replace('def util.f', 'def util.other'),
                    generated.replace('\nend Zerocopy', '\ndef extra := 1\nend Zerocopy'),
                    generated.replace('[zerocopy::util::f]', '[zerocopy::util::other]')):
            with self.assertRaises(ValueError):
                inline.split_live(bad, [ENTRY])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / ENTRY['file']
            source.parent.mkdir(parents=True)
            original = ('fn f() {\n' + BLOCK + '    let x = 0;\n}').replace('\n', '\r\n')
            source.write_bytes(original.encode())
            for folder in ('golden', 'scaffolding', 'live'):
                (root / 'verification/aeneas' / folder).mkdir(parents=True)
            live = root / 'verification/aeneas/live'
            for name in inline.golden.FILES:
                (live / name).write_text(generated if name == 'Funs.lean' else 'module\n')
            annotations = inline.discover(root, TOOL, [ENTRY])
            inline.update(root, [ENTRY], annotations, live)
            result = source.read_bytes().decode()
            self.assertIn('//     x + 1\r\n', result)
            self.assertEqual(original[original.index('    // proof:'):],
                             result[result.index('    // proof:'):])
            self.assertEqual(original[:original.index('    //   def')],
                             result[:result.index('    //   def')])
            annotations = inline.discover(root, TOOL, [ENTRY])
            inline.templates(root, [ENTRY])
            rendered = root / 'rendered'
            inline.render(root, annotations, rendered)
            self.assertEqual(inline.golden.compare(live, rendered), [])

    def test_llbc_binding_rejects_cfg_alternatives_stale_sources_and_missing_roots(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / ENTRY['file']
            path.parent.mkdir(parents=True)
            source = 'fn f() {\n' + BLOCK + '}\n'
            path.write_text(source)
            annotations = inline.discover(root, TOOL, [ENTRY])
            annotation = annotations[ENTRY['rust']]
            data = {'translated': {
                'files': [{'id': 1, 'name': {'Local': 'src/util/mod.rs'}, 'contents': source}],
                'fun_decls': [{'item_meta': {
                    'name': [{'Ident': [part, 0]} for part in ENTRY['rust'].split('::')],
                    'started_from': True, 'is_local': True,
                    'span': {'Untagged': {'generated_from_span': None, 'data': {
                        'file_id': 1, 'beg': {'line': 1, 'col': 0},
                        'end': {'line': annotation['end_line'], 'col': annotation['end_col']}}}}
                }}]}}
            llbc = root / 'crate.llbc'
            llbc.write_text(json.dumps(data))
            inline.check_bindings(root, annotations, llbc)
            for kind in ('alternative', 'stale', 'missing', 'duplicate', 'wrong_file'):
                bad = copy.deepcopy(data)
                translated = bad['translated']
                if kind == 'alternative':
                    translated['fun_decls'][0]['item_meta']['span']['Untagged']['data']['end']['line'] += 1
                elif kind == 'stale':
                    translated['files'][0]['contents'] += '// stale\n'
                elif kind == 'missing':
                    translated['fun_decls'] = []
                elif kind == 'duplicate':
                    translated['fun_decls'] *= 2
                else:
                    translated['files'][0]['name']['Local'] = 'src/other.rs'
                llbc.write_text(json.dumps(bad))
                with self.subTest(kind=kind), self.assertRaises(ValueError):
                    inline.check_bindings(root, annotations, llbc)


if __name__ == '__main__':
    unittest.main()
