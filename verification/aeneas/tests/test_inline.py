# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import copy
import json
import os
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'verification/aeneas'))
import inline

TOOL = Path(os.environ.get('AENEAS_INLINE_TOOL', ROOT / 'target/aeneas/annotation-tool/debug/aeneas-inline'))
BLOCK = ('/// ```aeneas\n'
         '/// spec f_spec\n'
         '///   ensures r => r = x\n'
         '/// ```\n')
ENTRY = {'file': 'zerocopy/src/util/mod.rs', 'syntax': 'f'}
RUST = 'zerocopy::util::f'
GENERATED = ('module\nnamespace Zerocopy\n'
             '/-- [zerocopy::util::f]:\n    Source: location -/\n'
             'def util.f (x : Nat) :=\n  x + 1\n\nend Zerocopy\n')


def syntax(source):
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / 'source.rs'
        path.write_bytes(source.encode())
        result = subprocess.run([str(TOOL)], input=json.dumps([str(path)]),
                                text=True, capture_output=True)
        if result.returncode:
            raise ValueError(result.stderr)
        return json.loads(result.stdout)[str(path)]


def fixture(root, source=None):
    source = BLOCK + 'fn f(x: usize) {}\n' if source is None else source
    path = root / ENTRY['file']
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)
    return inline.discover(root, TOOL)


def llbc(annotation, source):
    return {'translated': {
        'files': [{'id': 1, 'name': {'Local': 'src/util/mod.rs'}, 'contents': source}],
        'fun_decls': [{'generics': {'types': [], 'const_generics': [], 'trait_clauses': []},
                       'signature': {'inputs': ['type']},
                       'body': {'Structured': {'locals': {'arg_count': 1, 'locals': [
                           {'name': None}, {'name': 'x'}]}}},
                       'item_meta': {
                           'name': [{'Ident': [part, 0]} for part in RUST.split('::')],
                           'started_from': True, 'is_local': True,
                           'span': {'Untagged': {'generated_from_span': None, 'data': {
                               'file_id': 1, 'beg': {'line': 1, 'col': 0},
                               'end': {'line': annotation['end_line'], 'col': annotation['end_col']}}}}}}]}}


class InlineTests(unittest.TestCase):
    def setUp(self):
        patch = mock.patch('admission.inspect', return_value={'version': 1})
        patch.start()
        self.addCleanup(patch.stop)
        translation = mock.patch('admission.check_translation')
        translation.start()
        self.addCleanup(translation.stop)

    def parse(self, source):
        return inline.parse_file(source, syntax(source))

    def test_doc_ownership_crlf_unicode_attributes_and_source_map(self):
        for eol in ('\n', '\r\n'):
            source = ('const 雪: u8 = 0;\n/// Normal documentation.\n' + BLOCK +
                      '#[cfg(any())]\n#[allow(unused)]\nfn f(x: usize) {}').replace('\n', eol)
            found = self.parse(source)
            self.assertEqual(len(found), 1)
            self.assertEqual(found[0]['syntax'], 'f')
            self.assertEqual(found[0]['kind'], 'function')
            self.assertEqual(found[0]['spec_text'], 'spec f_spec\n  ensures r => r = x\n')
            self.assertEqual(found[0]['inputs'], ['x'])
            self.assertEqual(found[0]['ghosts'], [])
            self.assertEqual(found[0]['source_lines'], [4, 5])
            self.assertEqual(found[0]['newline'], eol)

    def test_source_snapshot_cannot_change_between_inspection_and_parsing(self):
        original = BLOCK + 'fn f(x: usize) {}'
        inspected = syntax(original)
        changed = original.replace('r = x', 'r ≠ x')
        with self.assertRaisesRegex(ValueError, 'Rust source changed during annotation inspection'):
            inline.parse_file(changed, inspected)
        del inspected['source']
        with self.assertRaisesRegex(ValueError, 'Rust source changed during annotation inspection'):
            inline.parse_file(original, inspected)

    def test_rejects_body_fences_orphans_unsupported_owners_and_duplicates(self):
        for source in ('fn f(x: usize) {\n' + BLOCK.replace('///', '//') + '}',
                       'fn outer() { ' + BLOCK + 'fn f(x: usize) {} }',
                       'impl Trait for S { ' + BLOCK + 'fn f(x: usize) {} }',
                       BLOCK + 'const X: usize = 1;',
                       BLOCK + 'type S = usize;',
                       BLOCK + 'mod m {}',
                       BLOCK + BLOCK + 'fn f(x: usize) {}'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.parse(source)

    def test_direct_include_str_is_rejected_in_owner_doc_expressions(self):
        for owner in ('fn f(x: usize) {}', 'struct Box(usize);', 'enum Box { Empty }'):
            for attr in ('#[doc = include_str!("contract.md")]',
                         '#[doc = std::include_str!("contract.md")]',
                         '#[doc = concat!("ordinary ", include_str!("contract.md"))]',
                         '#[doc = condVersionLink!(std::include_str!("contract.md"))]',
                         '#[cfg_attr(any(), doc = include_str!("contract.md"))]',
                         '#[cfg_attr(any(), cfg_attr(all(), doc = wrapper!(::std::include_str!("contract.md"))))]'):
                with self.subTest(owner=owner, attr=attr), self.assertRaisesRegex(
                        ValueError, 'Direct include_str!'):
                    self.parse(attr + '\n' + owner)
        # Visibility and cfg documentation flags do not supply computed strings.
        self.assertEqual(self.parse('#[doc(hidden)]\n#[cfg_attr(any(), doc(hidden))]\nfn f() {}'), [])

    def test_unannotated_computed_docs_are_outside_the_annotation_language(self):
        for owner in ('fn f(x: usize) {}', 'struct Box(usize);', 'enum Box { Empty }'):
            for attr in ('#[doc = concat!("ordinary ", "documentation")]',
                         '#[doc = condVersionLink!("version", "link")]',
                         '#[cfg_attr(any(), doc = condVersionLink!("version", "link"))]',
                         '#[cfg_attr(any(), cfg_attr(all(), doc = other_macro!("ordinary")))]',
                         '#[doc = codegen_header!("h5", "f")]',
                         '#[doc = codegen_section!(f, mutable = true)]',
                         '#[doc = concat!("include_str!(external text)")]'):
                with self.subTest(owner=owner, attr=attr):
                    self.assertEqual(self.parse(attr + '\n' + owner), [])

    def test_computed_docs_cannot_mix_with_literal_function_or_type_annotations(self):
        type_block = '/// ```aeneas\n/// model BoxValue := Fields\\ndecode self => self\n/// ```\n'
        for owner, block in (('fn f(x: usize) {}', BLOCK),
                             ('struct Box(usize);', type_block),
                             ('enum Box { Empty }', type_block)):
            for attr in ('#[doc = concat!("ordinary", " documentation")]',
                         '#[doc = condVersionLink!("version", "link")]',
                         '#[cfg_attr(any(), doc = condVersionLink!("version", "link"))]'):
                for docs in (attr + '\n' + block, block + attr + '\n'):
                    with self.subTest(owner=owner, docs=docs), self.assertRaisesRegex(
                            ValueError, 'Computed doc strings'):
                        self.parse(docs + owner)
        # Macro output supplies no source annotation; an empty extraction fails.
        with tempfile.TemporaryDirectory() as tmp, self.assertRaisesRegex(
                ValueError, 'No Aeneas specifications discovered'):
            fixture(Path(tmp), '#[doc = contract_docs!()]\nfn f(x: usize) {}')

    def test_literal_docs_are_owned_and_conditional_computed_and_inner_docs_rejected(self):
        source = '#[doc = "```aeneas\\nspec f_spec\\n  ensures r => r = x\\n```"]\nfn f(x: usize) {}'
        self.assertEqual(self.parse(source)[0]['spec_text'], 'spec f_spec\n  ensures r => r = x\n')
        for owner in ('struct Box(usize);', 'enum Box { Empty }'):
            source = '#[doc = "```aeneas\\nmodel BoxValue := Fields\\ndecode self => self\\n```"]\n' + owner
            self.assertEqual(self.parse(source)[0]['theorem'], 'BoxValue')
        for attr in ('#[cfg_attr(any(), doc = "```aeneas")]',
                     '#[doc = concat!("```", "aeneas")]',
                     '#[doc = concat!("```ae", "neas")]',
                     '#[cfg_attr(any(), doc = concat!("```ae", "neas"))]',
                     '#[doc = condVersionLink!("```ae", "neas")]',
                     '#[cfg_attr(any(), doc = condVersionLink!("```", "ae", "neas"))]',
                     '#[doc = include_str!("```aeneas")]',
                     '#![doc = "```aeneas"]'):
            for owner in ('fn f(x: usize) {}', 'struct Box(usize);', 'enum Box { Empty }'):
                with self.subTest(attr=attr, owner=owner), self.assertRaises(ValueError):
                    self.parse(attr + '\n' + owner)

    def test_block_doc_fences_and_non_doc_literal_lookalikes(self):
        for comment in ('/**\n```aeneas\nspec f_spec\n  ensures r => r = x\n```\n*/',
                        '/**\n * ```aeneas\n * spec f_spec\n *   ensures r => r = x\n * ```\n */'):
            self.assertEqual(self.parse(comment + '\nfn f(x: usize) {}')[0]['inputs'], ['x'])
        self.assertEqual(self.parse('#[cfg_attr(any(), arbitrary = "```aeneas")] fn f() {}'), [])

    def test_inherent_and_generic_ownership_automatically_introduces_rust_names(self):
        found = self.parse('mod m { impl<E> S<E> { ' + BLOCK + 'fn f(&self, x: usize) {} } }')
        self.assertEqual(found[0]['syntax'], 'm::S::f')
        self.assertEqual(found[0]['generics'], ['E'])
        for implementation in ('impl S<u8>', 'impl Trait for S', 'impl m::S'):
            with self.assertRaises(ValueError):
                self.parse(implementation + ' { ' + BLOCK + 'fn f(x: usize) {} }')
        for signature in ('fn f((x, y): (usize, usize)) {}', 'fn f(x: &mut usize) {}',
                          "fn f() -> &'static usize {}", 'fn f<const N: usize>() {}'):
            with self.assertRaises(ValueError):
                self.parse(BLOCK + signature)
        with self.assertRaises(ValueError):
            self.parse('impl S { ' + BLOCK + 'fn f(&mut self, x: usize) {} }')

    def test_ghosts_and_requirements_cannot_shadow_original_parameters(self):
        for header in ('(x : Nat)', '(T : Type)', '(ghost ghost : Nat)'):
            block = BLOCK.replace('spec f_spec', 'spec f_spec ' + header)
            with self.subTest(header=header), self.assertRaises(ValueError):
                self.parse(block + 'fn f<T>(x: T) {}')
        block = BLOCK.replace('spec f_spec', 'spec f_spec (ghost : Nat)')
        found = self.parse(block + 'fn f<T>(x: T) {}')[0]
        self.assertEqual(found['generics'], ['T'])
        self.assertEqual(found['ghosts'], ['ghost'])
        for requirements in ('///   requires x : True\n', '///   requires T : True\n',
                             '///   requires h : True\n///   requires h : True\n',
                             '///   aeneas_spec_end\n', '///     aeneas_spec_begin\n'):
            block = BLOCK.replace('///   ensures', requirements + '///   ensures')
            with self.subTest(requirements=requirements), self.assertRaises(ValueError):
                self.parse(block + 'fn f<T>(x: T) {}')

    def test_nominal_type_models_and_wrong_declaration_kinds(self):
        block = ('/// ```aeneas\n/// model BoxValue := Fields\n'
                 '/// decode self => self\n/// ```\n')
        for declaration, kind in (('struct Box<T>(T);', 'struct'), ('enum Box<T> { Some(T), None }', 'enum')):
            found = self.parse(block + declaration)[0]
            self.assertEqual(found['kind'], 'type')
            self.assertEqual(found['nominal_kind'], kind)
            self.assertEqual(found['generics'], ['T'])
            self.assertEqual(found['decoder_text'], 'self')
            self.assertEqual(found['value_binder'], 'self')
        for source in (BLOCK + 'struct Box<T>(T);', block + 'fn f(x: usize) {}',
                       block + 'type Box = usize;', block + 'union Box { x: usize }',
                       block.replace('decode self', 'decode T') + 'struct Box<T>(T);'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.parse(source)

    def test_plain_raw_clauses_multiple_posts_and_dependent_ghosts(self):
        text = ('spec f_spec (position : Fin self.length)\n'
                '  requires valid : position.val < self.length\n'
                '  requires(raw) bounded : self.val < 10\n'
                '  ensures out => out = self\n'
                '  ensures(raw) out => out.val = self.val\n')
        self.assertEqual(inline.parse_spec(text, [], ['self']), ('f_spec', 1))
        for bad in (text.replace('requires valid', 'requires(raw) self'),
                    text + '  requires late : True\n',
                    text.replace('ensures(raw)', 'ensures(other)'),
                    text.replace('requires(raw)', 'requires(other)'),
                    text.replace('  ensures out => out = self\n', '' ).replace('  ensures(raw) out => out.val = self.val\n', ''),
                    text + '  refines id to 0\n'):
            with self.subTest(text=bad), self.assertRaises(ValueError):
                inline.parse_spec(bad, [], ['self'])

    def test_model_shapes_decoders_and_extra_command_rejection(self):
        for shape in ('model BoxValue := Fields',
                      'model BoxValue where\n  value : TModel\n  positive : True'):
            for mode in ('decode', 'decode?'):
                text = shape + '\n' + mode + ' self =>\n  self\n'
                parsed = inline.parse_model(text, ['T'])
                self.assertEqual(parsed['shape_text'], shape)
                self.assertEqual(parsed['decoder_mode'], mode)
                self.assertEqual(parsed['decoder_text'], 'self')
                for command in ('axiom extra : False', 'def extra := 1', 'end',
                                'namespace Extra', 'open Classical', 'set_option maxRecDepth 0',
                                'model Extra := Nat', 'decode self => self', 'decode? self => none'):
                    with self.subTest(command=command), self.assertRaises(ValueError):
                        inline.parse_model(text + '  ' + command + '\n', ['T'])
        nested = inline.parse_model('model BoxValue := Nat\ndecode self =>\n  let word := self._0\n  let align := word + 1\n  align\n', [])
        self.assertEqual(nested['decoder_text'], 'let word := self._0\nlet align := word + 1\nalign')
        self.assertEqual(nested['decoder_line'], 2)
        for bad in ('model BoxValue := Fields\n',
                    'model BoxValue := Fields\ndecode self =>\n',
                    'model BoxValue := Fields\ndecode T => T\n',
                    'model T := Fields\ndecode self => self\n',
                    'model Fields := Fields\ndecode self => self\n',
                    'invariant old for self => True\n',
                    'model BoxValue := Fields\ndecode self => self\nextra command\n'):
            with self.subTest(text=bad), self.assertRaises(ValueError):
                inline.parse_model(bad, ['T'])

    def test_unannotated_functions_impls_and_macros_are_permitted(self):
        extras = ('fn missing() {}', '#[cfg(any())] fn inactive() {}',
                  'impl S { fn missing() {} methods!(); }',
                  '#[cfg(any())] impl S { #[cfg(any())] methods!(); }',
                  'impl S<u8> { fn missing() {} }', 'impl crate::S {}',
                  'impl Trait for S { methods!(); }',
                  '#[cfg(any())] mod m { impl S {} }', 'global_methods!();')
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for extra in extras:
                with self.subTest(extra=extra):
                    annotations = fixture(root, BLOCK + 'fn f(x: usize) {}\n' + extra)
                    self.assertEqual(set(annotations), {RUST})

    def test_discovery_snapshots_unannotated_sources_and_roots_only_annotations(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            annotations = fixture(root, 'struct S; impl S { ' + BLOCK + 'fn f(self) {} }')
            other = root / 'zerocopy/src/other.rs'
            other.write_text('#[cfg(any())] impl S { fn missed() {} }\nimpl Other { methods!(); }')
            ordinary = root / 'ordinary.rs'
            ordinary.write_text('fn unannotated() {}')
            annotations = inline.discover(root, TOOL)
            self.assertEqual(set(annotations), {'zerocopy::util::S::f'})
            self.assertEqual(set(annotations.source_snapshots), {ENTRY['file'], 'zerocopy/src/other.rs'})
            self.assertEqual([a['rust'] for a in annotations.types], ['zerocopy::util::S'])
            work = root / 'work'
            work.mkdir()
            inline.write_scan(annotations, work)
            self.assertEqual((work / 'roots.txt').read_text(), 'zerocopy::util::S::f\n')
            self.assertEqual(json.loads((work / 'source-types.json').read_text()), annotations.types)
            # Literal lookalikes outside the crate are inspected without becoming
            # roots; a real reserved fence there has no supported source owner.
            ordinary.write_text('const TEXT: &str = "```aeneas";')
            annotations = inline.discover(root, TOOL)
            self.assertIn('ordinary.rs', annotations.source_snapshots)
            ordinary.write_text(BLOCK + 'fn outside(x: usize) {}')
            with self.assertRaisesRegex(ValueError, 'Unsupported annotated source location'):
                inline.discover(root, TOOL)

    def test_present_nominal_model_adds_only_its_exact_type_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            model = '/// ```aeneas\n/// model SValue := Fields\n/// decode self => self\n/// ```\n'
            source = model + 'struct S;\n' + BLOCK + 'fn f(x: usize) {}'
            annotations = fixture(root, source)
            self.assertEqual(set(annotations), {'zerocopy::util::S', RUST})
            work = root / 'work'
            work.mkdir()
            inline.write_scan(annotations, work)
            self.assertEqual((work / 'roots.txt').read_text(), RUST + ',zerocopy::util::S\n')
            # The nominal owner remains available to structural model binding
            # after its authored model is removed, but is no longer a root.
            annotations = fixture(root, source.removeprefix(model))
            self.assertEqual(set(annotations), {RUST})
            self.assertEqual([a['rust'] for a in annotations.types], ['zerocopy::util::S'])

    def test_nested_annotations_select_exact_owner_without_type_wildcards(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = 'mod m { struct S; impl S { ' + BLOCK + 'fn f(self) {} } }'
            annotations = fixture(root, source)
            self.assertEqual(set(annotations), {'zerocopy::util::m::S::f'})
            work = root / 'work'
            work.mkdir()
            inline.write_scan(annotations, work)
            self.assertEqual((work / 'roots.txt').read_text(), 'zerocopy::util::m::S::f\n')

    def test_removing_an_annotation_visibly_removes_its_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            extra = BLOCK.replace('f_spec', 'g_spec') + 'fn g(x: usize) {}\n'
            annotations = fixture(root, BLOCK + 'fn f(x: usize) {}\n' + extra)
            self.assertEqual(set(annotations), {RUST, 'zerocopy::util::g'})
            annotations = fixture(root, 'fn f(x: usize) {}\n' + extra)
            self.assertEqual(set(annotations), {'zerocopy::util::g'})
            work = root / 'work'
            work.mkdir()
            inline.write_scan(annotations, work)
            self.assertEqual((work / 'roots.txt').read_text(), 'zerocopy::util::g\n')
            with self.assertRaisesRegex(ValueError, 'No Aeneas specifications discovered'):
                fixture(root, 'fn f(x: usize) {}\nfn g(x: usize) {}')

    def test_rejects_near_miss_guards_legacy_sections_and_extra_commands(self):
        variants = [BLOCK.replace('```aeneas', guard) for guard in
                    ('```Aeneas', '```aeneos', '``aeneas', '```aeneas v2')]
        variants += [BLOCK.replace('/// ```\n', ''),
                     BLOCK.replace('/// ```\n', '/// ``` trailing\n'),
                     BLOCK.replace('///   ensures', '/// ensures'),
                     BLOCK.replace('///   ensures', '///   for util.other x\n///   ensures'),
                     BLOCK.replace('///   ensures', '///   proof:\n///   ensures'),
                     BLOCK.replace('/// spec', '/// model:\n/// spec'),
                     BLOCK.replace('/// ```\n', '/// def extra := 1\n/// ```\n')]
        for block in variants:
            with self.subTest(block=block), self.assertRaises(ValueError):
                self.parse(block + 'fn f(x: usize) {}')

    def test_fake_fences_in_literals_are_not_annotations(self):
        self.assertEqual(self.parse('fn f() { let x = r###"\n' + BLOCK + '"###; }'), [])
        with self.assertRaises(ValueError):
            self.parse('fn f() { /* ```aeneas\nspec f_spec\n``` */ }')

    def test_discovery_derives_ids_and_rejects_duplicates_or_unsupported_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            annotations = fixture(root)
            self.assertEqual(set(annotations), {RUST})
            self.assertNotIn('golden', annotations[RUST])
            self.assertNotIn('depends_on', annotations[RUST])
            path = root / ENTRY['file']
            path.write_text('fn f(x: usize) {}')
            with self.assertRaisesRegex(ValueError, 'No Aeneas specifications discovered'):
                inline.discover(root, TOOL)
            fixture(root)
            path.write_text(path.read_text() * 2)
            with self.assertRaisesRegex(ValueError, 'Duplicate annotation'):
                inline.discover(root, TOOL)
            fixture(root)
            (root / 'unsupported.rs').write_text(BLOCK + 'fn f(x: usize) {}')
            with self.assertRaisesRegex(ValueError, 'Unsupported annotated'):
                inline.discover(root, TOOL)

    def test_models_derive_root_names_and_verify_parameter_order(self):
        annotations = {RUST: {'generics': [], 'inputs': ['x']}}
        self.assertEqual(inline.generated_bindings(GENERATED, annotations), {RUST: 'util.f'})
        for bad in (GENERATED.replace('(x : Nat)', '(other : Nat)'),
                    GENERATED.replace('[zerocopy::util::f]', '[zerocopy::util::other]'),
                    GENERATED.replace('\nend Zerocopy', GENERATED + '\nend Zerocopy')):
            with self.assertRaises(ValueError):
                inline.generated_bindings(bad, annotations)
        two = GENERATED.replace('(x : Nat)', '(a b : Nat)').replace('x + 1', 'a + b')
        original = {RUST: {'generics': [], 'inputs': ['a', 'b']}}
        self.assertEqual(inline.generated_bindings(two, original), {RUST: 'util.f'})
        with self.assertRaisesRegex(ValueError, 'parameters disagree'):
            inline.generated_bindings(two.replace('(a b : Nat)', '(b a : Nat)'), original)
        generic = GENERATED.replace('[zerocopy::util::f]', '[zerocopy::util::{zerocopy::util::S<E>}::f]')
        generic = generic.replace('def util.f (x : Nat)', 'def util.S.f {E : Type} (self : S E)')
        name = 'zerocopy::util::S::f'
        self.assertEqual(inline.generated_bindings(generic, {name: {'generics': ['E'], 'inputs': ['self']}}), {name: 'util.S.f'})
        with self.assertRaises(ValueError):
            inline.generated_bindings(generic.replace('{zerocopy::util::S<E>}', '{zerocopy::other::S<E>}'), {name: {'generics': ['E'], 'inputs': ['self']}})

    def test_loop_helpers_dependencies_and_constants_do_not_replace_roots(self):
        helpers = ('/-- [zerocopy::util::f]: loop body 0:\n    Source: x -/\n'
                   '@[rust_loop_body]\ndef util.f_loop.body := 1\n\n'
                   '/-- [zerocopy::util::dependency]:\n    Source: x -/\n'
                   'def util.dependency := 4\n\n')
        self.assertEqual(inline.generated_bindings(GENERATED.replace('/-- ', helpers + '/-- ', 1),
                                                  {RUST: {'generics': [], 'inputs': ['x']}}), {RUST: 'util.f'})
        annotations = {RUST: {'generics': [], 'inputs': ['x']}}
        root = GENERATED.replace('def util.f', '@[reducible]\ndef util.f')
        self.assertEqual(inline.generated_bindings(root, annotations), {RUST: 'util.f'})
        with self.assertRaisesRegex(ValueError, 'Unsupported generated root'):
            inline.generated_bindings(root.replace('reducible', 'unknown'), annotations)

    def test_trait_implementation_dependencies_do_not_replace_roots(self):
        annotations = {RUST: {'generics': [], 'inputs': ['x']}}
        trait = 'zerocopy::{impl zerocopy::PointerMetadata for ()}::from_elem_count'
        dependency = (f'/-- [{trait}]:\n    Source: location -/\n'
                      'def Tuple.Insts.ZerocopyPointerMetadata.from_elem_count '
                      '(elems : Nat) := ()\n\n')
        source = GENERATED.replace('/-- ', dependency + '/-- ', 1)
        self.assertEqual(inline.generated_bindings(source, annotations), {RUST: 'util.f'})
        # Neither a dependency alone nor an unsupported trait owner can stand
        # in for the mandatory source-to-model binding of an annotated item.
        missing_root = 'module\nnamespace Zerocopy\n' + dependency + 'end Zerocopy\n'
        with self.assertRaisesRegex(ValueError, 'do not match discovered specifications'):
            inline.generated_bindings(missing_root, annotations)
        with self.assertRaisesRegex(ValueError, 'do not match discovered specifications'):
            inline.generated_bindings(source, {trait: {'generics': [], 'inputs': ['elems']}})

    def test_assembly_requires_independent_checker_before_generation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            work = root / 'work'
            work.mkdir()
            with self.assertRaisesRegex(ValueError, 'RequiredContracts.lean is required'):
                inline.assemble(root, {}, work)
            self.assertFalse((work / 'Specs.lean').exists())
            self.assertFalse((work / 'Required.lean').exists())

    def test_development_assembly_preserves_edited_projection_and_all_outputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            annotations = fixture(root)
            work = root / 'work'
            (work / 'Zerocopy').mkdir(parents=True)
            (work / 'Zerocopy/Funs.lean').write_text(GENERATED)
            lean = root / 'verification/aeneas/lean'
            lean.mkdir(parents=True)
            (lean / 'RequiredContracts.lean').write_text('')
            inline.save_bindings(root, annotations, work, development=True)
            inline.assemble(root, annotations, work, development=True)
            self.assertTrue((work / inline.workspace.PROJECTION_STATE).exists())
            inline.assemble(root, annotations, work, development=True)
            for module in inline.workspace.PROJECTIONS:
                path = work / f'{module}.lean'
                original = path.read_bytes()
                path.write_bytes(original + b'\n-- local scratch edit\n')
                before = {str(p.relative_to(work)): p.read_bytes() for p in work.rglob('*') if p.is_file()}
                with self.subTest(module=module), self.assertRaisesRegex(ValueError, 'Refusing to overwrite'):
                    inline.assemble(root, annotations, work, development=True)
                self.assertEqual(before, {str(p.relative_to(work)): p.read_bytes() for p in work.rglob('*') if p.is_file()})
                path.write_bytes(original)

    def test_assembly_injects_verified_application_and_maps_lines_and_modules(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            annotations = fixture(root)
            work = root / 'work'
            (work / 'Zerocopy').mkdir(parents=True)
            (work / 'Zerocopy/Funs.lean').write_text(GENERATED)
            proofs = root / 'verification/aeneas/lean/Proofs'
            proofs.mkdir(parents=True)
            (proofs / 'Util.lean').write_text('import Specs\n')
            (root / 'verification/aeneas/lean/RequiredContracts.lean').write_text('')
            (root / 'verification/aeneas/lean/ExtraFacts.lean').write_text(
                'namespace Other\naxiom unused : True\nend Other\n')
            with self.assertRaisesRegex(ValueError, 'Verified live'):
                inline.assemble(root, annotations, work)
            inline.save_bindings(root, annotations, work)
            inline.assemble(root, annotations, work)
            specs = (work / 'Specs.lean').read_text()
            self.assertIn('aeneas_spec_begin\nspec f_spec', specs)
            self.assertIn('ensures r => r = x\naeneas_spec_end', specs)
            self.assertIn('check_spec_binding Zerocopy.Specs.f_spec for Zerocopy.util.f with 1', specs)
            self.assertIn('spec f_spec\n  for @Zerocopy.util.f with 0 type parameters\n  ensures', specs)
            required = (work / 'Required.lean').read_text()
            self.assertIn('example : Zerocopy.Specs.f_spec := @Zerocopy.Proofs.f_spec', required)
            self.assertIn('check_contract Zerocopy.Obligations.f_spec using @Zerocopy.Proofs.f_spec', required)
            self.assertNotIn('def requiredTheorems ', required)
            self.assertLess(required.index('example : Zerocopy.Specs.f_spec'),
                            required.index('check_contract Zerocopy.Obligations.f_spec'))
            self.assertIn('proofModuleNames : Array Name := #[`Proofs, `Proofs.Util]', required)
            self.assertIn('import ExtraFacts', required)
            self.assertIn('auditModuleNames : Array Name := #[`ExtraFacts', required)
            mapping = json.loads((work / 'Specs.source-map.json').read_text())
            for index, line in enumerate(specs.splitlines(), 1):
                if line.startswith('spec '):
                    self.assertEqual(mapping[str(index)], {'file': ENTRY['file'], 'line': 2})
                if line.startswith('  for '):
                    self.assertEqual(mapping[str(index)], {'file': ENTRY['file'], 'line': 2})
                if line.startswith('  ensures '):
                    self.assertEqual(mapping[str(index)], {'file': ENTRY['file'], 'line': 3})
            # Comment-only golden variation is allowed, but code and source
            # changes invalidate the mapping before any proof is compiled.
            (work / 'Zerocopy/Funs.lean').write_text('-- moved\n' + GENERATED)
            inline.assemble(root, annotations, work)
            (work / 'Zerocopy/Funs.lean').write_text(GENERATED.replace('x + 1', 'x + 2'))
            with self.assertRaisesRegex(ValueError, 'stale'):
                inline.assemble(root, annotations, work)
            (work / 'Zerocopy/Funs.lean').write_text(GENERATED)
            (root / ENTRY['file']).write_text((root / ENTRY['file']).read_text() + '// changed\n')
            with self.assertRaisesRegex(ValueError, 'changed after annotation discovery'):
                inline.assemble(root, annotations, work)

    def test_fixed_source_snapshot_rejects_discovery_digest_binding_and_assembly_edits(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            annotations = fixture(root)
            original = (root / ENTRY['file']).read_bytes()
            digest = inline.source_digest(root, annotations)
            self.assertEqual(annotations.source_snapshots[ENTRY['file']], original)
            work = root / 'work'
            (work / 'Zerocopy').mkdir(parents=True)
            (work / 'Zerocopy/Funs.lean').write_text(GENERATED)
            (root / 'verification/aeneas/lean').mkdir(parents=True)
            (root / 'verification/aeneas/lean/RequiredContracts.lean').write_text('')
            inline.save_bindings(root, annotations, work)
            extracted = root / 'crate.llbc'
            extracted.write_text(json.dumps(llbc(annotations[RUST], original.decode())))
            changed = original.replace(b'r = x', b'r != x')
            (root / ENTRY['file']).write_bytes(changed)
            for operation in (lambda: inline.source_digest(root, annotations),
                              lambda: inline.save_bindings(root, annotations, work),
                              lambda: inline.assemble(root, annotations, work),
                              lambda: inline.check_bindings(root, annotations, extracted)):
                with self.assertRaisesRegex(ValueError, 'changed after annotation discovery'):
                    operation()
            self.assertEqual(annotations[RUST]['spec_text'], 'spec f_spec\n  ensures r => r = x\n')
            self.assertEqual(json.loads((work / 'bindings.json').read_text())['sources'], digest)
            (root / ENTRY['file']).write_bytes(original)
            self.assertEqual(inline.source_digest(root, annotations), digest)

    def test_unannotated_dependency_files_are_frozen_and_checked_against_charon(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root)
            dependency = root / 'zerocopy/src/util/macros.rs'
            dependency.write_text('fn dependency() -> usize { 1 }\n')
            annotations = inline.discover(root, TOOL)
            digest = inline.source_digest(root, annotations)
            source = (root / ENTRY['file']).read_text()
            data = llbc(annotations[RUST], source)
            data['translated']['files'].extend([
                {'id': 2, 'name': {'Local': 'src/util/macros.rs'}, 'contents': dependency.read_text()},
                {'id': 3, 'name': {'Local': '/rustc/library/core/src/lib.rs'}, 'contents': None}])
            path = root / 'crate.llbc'
            path.write_text(json.dumps(data))
            inline.check_bindings(root, annotations, path)
            dependency.write_text('fn dependency() -> usize { 2 }\n')
            with self.assertRaisesRegex(ValueError, 'changed after annotation discovery'):
                inline.source_digest(root, annotations)
            with self.assertRaisesRegex(ValueError, 'changed after annotation discovery'):
                inline.check_bindings(root, annotations, path)
            dependency.write_bytes(annotations.source_snapshots['zerocopy/src/util/macros.rs'])
            self.assertEqual(inline.source_digest(root, annotations), digest)
            for change, expected in [('stale', 'different source body for local dependency'),
                                     ('missing', 'missing source contents'),
                                     ('unscanned', 'lacks an inspected source snapshot')]:
                bad = copy.deepcopy(data)
                file = bad['translated']['files'][1]
                if change == 'stale':
                    file['contents'] = file['contents'].replace('{ 1 }', '{ 2 }')
                elif change == 'missing':
                    file['contents'] = None
                else:
                    file['name'] = {'Local': 'src/unscanned.rs'}
                path.write_text(json.dumps(bad))
                with self.subTest(change=change), self.assertRaisesRegex(ValueError, expected):
                    inline.check_bindings(root, annotations, path)

    def test_type_binding_order_structural_coverage_and_model_assembly(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            block = '/// ```aeneas\n/// model BoxValue := Fields\n/// decode self => self\n/// ```\n'
            source = block + 'struct Box<T>(T);\nenum E { A }\n' + BLOCK + 'fn f(x: usize) {}\n'
            annotations = fixture(root, source)
            self.assertEqual(len(annotations.types), 2)
            data = llbc(annotations[RUST], source)
            for index, owner in enumerate(annotations.types):
                data['translated'].setdefault('type_decls', []).append({
                    'def_id': index, 'generics': {'types': [{'name': name} for name in owner['generics']],
                                                'const_generics': [], 'trait_clauses': []},
                    'kind': {'Struct' if owner['nominal_kind'] == 'struct' else 'Enum': []},
                    'item_meta': {'name': [{'Ident': [part, 0]} for part in owner['rust'].split('::')],
                                  'is_local': True, 'started_from': owner['rust'] in annotations,
                                  'span': {'Untagged': {'generated_from_span': None, 'data': {
                                      'file_id': 1, 'beg': {'line': owner['open_line'], 'col': 0},
                                      'end': {'line': owner['end_line'], 'col': owner['end_col']}}}}}})
            path = root / 'crate.llbc'
            path.write_text(json.dumps(data))
            inline.check_bindings(root, annotations, path)
            work = root / 'work'
            (work / 'Zerocopy').mkdir(parents=True)
            (work / 'Zerocopy/Funs.lean').write_text(GENERATED)
            types = ('module\nnamespace Zerocopy\n'
                     '/-- [zerocopy::util::E]\n Source: x -/\n@[discriminant isize]\n'
                     'inductive util.E where\n| A : util.E\n'
                     '/-- [zerocopy::util::Box]\n Source: x -/\n'
                     'structure util.Box (T : Type) where\n  val : T\n\nend Zerocopy\n')
            (work / 'Zerocopy/Types.lean').write_text(types)
            inline.save_bindings(root, annotations, work)
            manifest = json.loads((work / 'bindings.json').read_text())
            self.assertEqual(manifest['version'], 3)
            self.assertEqual([row['category'] for row in manifest['type_image']],
                             ['local-nominal', 'local-nominal'])
            self.assertEqual([rust for rust, entry in manifest['bindings'].items() if entry['kind'] == 'type'],
                             ['zerocopy::util::E', 'zerocopy::util::Box'])
            self.assertEqual(manifest['bindings']['zerocopy::util::Box']['model'], 'Zerocopy.util.Box.BoxValue')
            (root / 'verification/aeneas/lean').mkdir(parents=True)
            (root / 'verification/aeneas/lean/RequiredContracts.lean').write_text('')
            inline.assemble(root, annotations, work)
            shapes = (work / 'ModelShapes.lean').read_text()
            models = (work / 'Models.lean').read_text()
            self.assertIn('aeneas_model_shape Zerocopy.util.Box with 1 type parameters begin\nmodel BoxValue := Fields\nend', shapes)
            self.assertIn('derive_rust_model Zerocopy.util.Box with 1 type parameters decode self =>\n  self', models)
            default = manifest['bindings']['zerocopy::util::E']
            self.assertEqual(default['model'], default['fields'])
            self.assertEqual(default['provider'], 'Zerocopy.util.E.aeneasModel')
            for module, generated in [('ModelShapes', shapes), ('Models', models)]:
                mapping = json.loads((work / f'{module}.source-map.json').read_text())
                for line, location in mapping.items():
                    self.assertLessEqual(int(line), len(generated.splitlines()))
                    self.assertEqual(location['file'], ENTRY['file'])
            required = (work / 'Required.lean').read_text()
            self.assertNotIn('Zerocopy.Proofs.BoxValue', required)
            self.assertIn('import Models', required)
            (work / 'Zerocopy/Types.lean').write_text(types.replace('val : T', 'val : Option T'))
            with self.assertRaisesRegex(ValueError, 'stale'):
                inline.assemble(root, annotations, work)
            # An unannotated nominal carrier cannot vanish into an alias.
            (work / 'Zerocopy/Types.lean').write_text(types.replace('inductive util.E where\n| A : util.E', 'def util.E := Unit'))
            with self.assertRaisesRegex(ValueError, 'nominal type declarations'):
                inline.save_bindings(root, annotations, work)
            (work / 'Zerocopy/Types.lean').write_text(types)
            for change in ('missing', 'kind', 'span', 'generic'):
                bad = copy.deepcopy(data)
                if change == 'missing':
                    bad['translated']['type_decls'].pop(0)
                elif change == 'kind':
                    bad['translated']['type_decls'][1]['kind'] = {'Struct': []}
                elif change == 'span':
                    bad['translated']['type_decls'][1]['item_meta']['span']['Untagged']['data']['end']['line'] += 1
                else:
                    bad['translated']['type_decls'][0]['generics']['types'] = []
                path.write_text(json.dumps(bad))
            with self.subTest(change=change), self.assertRaises(ValueError):
                    inline.check_bindings(root, annotations, path)

    def test_macro_expanded_nominal_dependencies_require_exact_safe_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = ('macro_rules! make { ($name:ident) => { struct $name<O>(O); }; }\n'
                      + BLOCK + 'fn f(x: usize) {}\n')
            annotations = fixture(root, source)
            self.assertEqual(len(annotations.macros), 1)
            self.assertFalse(any(t['rust'] == 'zerocopy::util::U16' for t in annotations.types))
            data = llbc(annotations[RUST], source)
            line = source.splitlines()[0]
            start, end = line.index('struct $name'), line.index('struct $name') + len('struct $name<O>(O);')
            declaration = {
                'def_id': 10, 'src': 'Normal',
                'generics': {'regions': [], 'types': [{'name': 'O'}], 'const_generics': [],
                             'trait_clauses': []},
                'kind': {'Struct': [{'ty': {'Value': [17, {'TypeVar': {'Free': 0}}]}}]},
                'item_meta': {
                    'name': [{'Ident': [part, 0]} for part in 'zerocopy::util::U16'.split('::')],
                    'is_local': True, 'started_from': False, 'source_text': None,
                    'span': {'Untagged': {'generated_from_span': None, 'data': {
                        'file_id': 1, 'beg': {'line': 1, 'col': start},
                        'end': {'line': 1, 'col': end}}}}}
            }
            data['translated']['type_decls'] = [declaration]
            path = root / 'crate.llbc'
            path.write_text(json.dumps(data))
            inline.check_bindings(root, annotations, path)
            candidate = annotations.extracted_types['zerocopy::util::U16']
            self.assertTrue(candidate['macro_expanded'])
            self.assertEqual(candidate['syntax'], 'U16')

            work = root / 'work'
            (work / 'Zerocopy').mkdir(parents=True)
            (work / 'Zerocopy/Funs.lean').write_text(GENERATED)
            (work / 'Zerocopy/Types.lean').write_text(
                'module\nnamespace Zerocopy\n'
                '/-- [zerocopy::util::U16]\n Source: x -/\n'
                'structure util.U16 (O : Type) where\n  val : O\n\nend Zerocopy\n')
            inline.save_bindings(root, annotations, work)
            binding = json.loads((work / 'bindings.json').read_text())['bindings']['zerocopy::util::U16']
            self.assertTrue(binding['macro_expanded'])
            self.assertEqual(binding['file'], ENTRY['file'])

            for change in ('span', 'source', 'generated', 'text', 'const', 'trait',
                           'reference', 'function_pointer', 'deduplicated_reference', 'ordinary_owner'):
                bad = copy.deepcopy(data)
                item = bad['translated']['type_decls'][0]
                if change == 'span':
                    item['item_meta']['span']['Untagged']['data']['end']['col'] = len(line)
                elif change == 'source':
                    bad['translated']['files'][0]['contents'] += '// stale\n'
                elif change == 'generated':
                    item['item_meta']['span']['Untagged']['generated_from_span'] = {}
                elif change == 'text':
                    item['item_meta']['source_text'] = 'struct U16;'
                elif change == 'const':
                    item['generics']['const_generics'] = [{'name': 'N'}]
                elif change == 'trait':
                    item['generics']['trait_clauses'] = [{}]
                elif change == 'reference':
                    item['kind']['Struct'][0]['ty'] = {'Ref': []}
                elif change == 'function_pointer':
                    item['kind']['Struct'][0]['ty'] = {'FnPtr': []}
                elif change == 'deduplicated_reference':
                    item['kind']['Struct'][0]['ty'] = {'Deduplicated': 17}
                    bad['translated']['type_decls'].append({
                        'def_id': 11, 'item_meta': {'is_local': False, 'name': []},
                        'kind': {'Struct': [{'ty': {'Value': [17, {'Ref': []}]}}]},
                    })
                else:
                    ordinary = 'struct U16;\n' + source
                    (root / ENTRY['file']).write_text(ordinary)
                    other_annotations = fixture(root, ordinary)
                    bad['translated']['files'][0]['contents'] = ordinary
                    bad['translated']['fun_decls'][0]['item_meta']['span']['Untagged']['data']['end']['line'] += 1
                    item['item_meta']['span']['Untagged']['data']['beg']['line'] += 1
                    item['item_meta']['span']['Untagged']['data']['end']['line'] += 1
                    path.write_text(json.dumps(bad))
                    with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'exact supported Rust source ownership'):
                        inline.check_bindings(root, other_annotations, path)
                    (root / ENTRY['file']).write_text(source)
                    continue
                path.write_text(json.dumps(bad))
                with self.subTest(change=change), self.assertRaises(ValueError):
                    inline.check_bindings(root, annotations, path)

            decorated = source.replace('struct $name<O>(O);', '#[doc = "```aeneas"] struct $name<O>(O);')
            decorated_annotations = fixture(root, decorated)
            decorated_data = llbc(decorated_annotations[RUST], decorated)
            item = copy.deepcopy(declaration)
            decorated_line = decorated.splitlines()[0]
            item['item_meta']['span']['Untagged']['data']['beg']['col'] = decorated_line.index('struct $name')
            item['item_meta']['span']['Untagged']['data']['end']['col'] = (
                decorated_line.index('struct $name') + len('struct $name<O>(O);'))
            decorated_data['translated']['type_decls'] = [item]
            path.write_text(json.dumps(decorated_data))
            with self.assertRaisesRegex(ValueError, 'exact supported Rust source ownership'):
                inline.check_bindings(root, decorated_annotations, path)

    def test_raw_type_image_classifies_traits_and_external_nominals(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            annotations = fixture(root)
            source = (root / ENTRY['file']).read_text()
            data = llbc(annotations[RUST], source)
            def meta(rust, local):
                return {'name': [{'Ident': [part, 0]} for part in rust.split('::')],
                        'is_local': local}
            data['translated']['trait_decls'] = [
                {'def_id': 10, 'item_meta': meta('zerocopy::util::Dictionary', True)}]
            data['translated']['type_decls'] = [
                {'def_id': 11, 'item_meta': meta('core::marker::PhantomData', False),
                 'kind': {'Struct': []}, 'generics': {'types': [{'name': 'T'}]}}]
            llbc_path = root / 'crate.llbc'
            llbc_path.write_text(json.dumps(data))
            inline.check_bindings(root, annotations, llbc_path)
            work = root / 'work'
            (work / 'Zerocopy').mkdir(parents=True)
            (work / 'Zerocopy/Funs.lean').write_text(GENERATED)
            types = ('module\nnamespace Zerocopy\n'
                     '/-- [core::marker::PhantomData]\n Source: x -/\n'
                     '@[rust_type "core::marker::PhantomData"]\n'
                     'structure core.marker.PhantomData (T : Type) where\n\n'
                     '/-- Trait declaration: [zerocopy::util::Dictionary]\n Source: x -/\n'
                     'structure util.Dictionary (Self : Type) (Assoc : Type) where\n\n'
                     'end Zerocopy\n')
            path = work / 'Zerocopy/Types.lean'
            path.write_text(types)
            inline.save_bindings(root, annotations, work)
            rows = json.loads((work / 'bindings.json').read_text())['type_image']
            self.assertEqual([(row['category'], row['parameters']) for row in rows],
                             [('external-nominal', 1), ('trait-dictionary', 2)])
            classes = annotations.type_classes
            annotations.type_classes = None
            with self.assertRaisesRegex(ValueError, 'checked LLBC classification'):
                inline.save_bindings(root, annotations, work)
            annotations.type_classes = classes
            for changed in (types.replace('Trait declaration: ', ''),
                            types.replace('@[rust_type "core::marker::PhantomData"]\n', ''),
                            types.replace('PhantomData (T : Type)', 'PhantomData (T : Type) (U : Type)'),
                            types.replace('core.marker.PhantomData', 'core.marker.Other', 1)):
                path.write_text(changed)
                with self.assertRaises(ValueError):
                    inline.save_bindings(root, annotations, work)
            path.write_text(types)
            annotations.type_classes.pop('zerocopy::util::Dictionary')
            with self.assertRaisesRegex(ValueError, 'classified extraction ownership'):
                inline.save_bindings(root, annotations, work)

    def test_two_type_owners_can_choose_the_same_short_model_name(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            model = '/// ```aeneas\n/// model SharedName := Fields\n/// decode self => self\n/// ```\n'
            source = model + 'struct Left(usize);\n' + model + 'struct Right(usize);\n' + BLOCK + 'fn f(x: usize) {}\n'
            annotations = fixture(root, source)
            self.assertEqual(annotations['zerocopy::util::Left']['model_name'], 'SharedName')
            self.assertEqual(annotations['zerocopy::util::Right']['model_name'], 'SharedName')
            self.assertEqual(len(annotations), 3)

    def test_whole_module_goldens_update_without_rewriting_rust(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root)
            original = (root / ENTRY['file']).read_bytes()
            live = root / 'live'
            live.mkdir()
            for name in inline.golden.FILES:
                (live / name).write_text(GENERATED if name == 'Funs.lean' else 'module\n')
            inline.update(root, live)
            self.assertEqual((root / ENTRY['file']).read_bytes(), original)
            inline.check_goldens(root)
            rendered = root / 'rendered'
            inline.render(root, rendered)
            self.assertEqual(inline.golden.compare(live, rendered), [])
            (root / 'verification/aeneas/golden/obsolete.lean.in').write_text('placeholder')
            with self.assertRaises(ValueError):
                inline.check_goldens(root)

    def test_llbc_binding_rejects_cfg_alternatives_stale_sources_and_parameter_changes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            annotations = fixture(root)
            source = (root / ENTRY['file']).read_text()
            data = llbc(annotations[RUST], source)
            path = root / 'crate.llbc'
            path.write_text(json.dumps(data))
            inline.check_bindings(root, annotations, path)
            for kind in ('alternative', 'stale', 'missing', 'duplicate', 'wrong_file', 'generic', 'arg_name', 'arg_count'):
                bad = copy.deepcopy(data)
                translated = bad['translated']
                function = translated['fun_decls'][0]
                if kind == 'alternative':
                    function['item_meta']['span']['Untagged']['data']['end']['line'] += 1
                elif kind == 'stale':
                    translated['files'][0]['contents'] += '// stale\n'
                elif kind == 'missing':
                    translated['fun_decls'] = []
                elif kind == 'duplicate':
                    translated['fun_decls'] *= 2
                elif kind == 'wrong_file':
                    translated['files'][0]['name']['Local'] = 'src/other.rs'
                elif kind == 'generic':
                    function['generics']['types'] = [{'name': 'T'}]
                elif kind == 'arg_name':
                    function['body']['Structured']['locals']['locals'][1]['name'] = 'other'
                else:
                    function['body']['Structured']['locals']['arg_count'] = 2
                path.write_text(json.dumps(bad))
                with self.subTest(kind=kind), self.assertRaises(ValueError):
                    inline.check_bindings(root, annotations, path)

    def test_extraction_rejects_extra_roots_and_permits_unannotated_dependencies(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            annotations = fixture(root)
            source = (root / ENTRY['file']).read_text()
            data = llbc(annotations[RUST], source)
            initializer = copy.deepcopy(data['translated']['fun_decls'][0])
            initializer['src'] = {'GlobalInitializer': {'id': 0, 'generics': {}}}
            initializer['item_meta']['name'][-1]['Ident'][0] = 'CONSTANT'
            data['translated']['fun_decls'].append(initializer)
            path = root / 'crate.llbc'
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'Extracted roots do not match'):
                inline.check_bindings(root, annotations, path)
            initializer['item_meta']['started_from'] = False
            path.write_text(json.dumps(data))
            inline.check_bindings(root, annotations, path)
            initializer['item_meta']['started_from'] = True
            initializer['src'] = 'Normal'
            initializer['item_meta']['name'][-1]['Ident'][0] = 'generated_method'
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'Extracted roots do not match'):
                inline.check_bindings(root, annotations, path)

    def test_inherent_method_llbc_identity_resolves_named_self(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            block = BLOCK.replace('(x : Nat)', '(self : S)')
            source = 'struct S; impl S { ' + block + 'fn f(self) {} }\n'
            annotations = fixture(root, source)
            annotation = annotations['zerocopy::util::S::f']
            data = llbc(annotation, source)
            translated = data['translated']
            type_name = [{'Ident': [part, 0]} for part in ['zerocopy', 'util', 'S']]
            body = {'Adt': {'id': 1, 'builtin': None,
                            'generics': {'regions': [], 'types': [], 'const_generics': [], 'trait_refs': []}}}
            implementation = {'Ty': {'kind': 'InherentImplBlock', 'params': {'types': [], 'regions': []},
                                     'skip_binder': {'Deduplicated': 3}}}
            translated['item_names'] = [{'value': {'Value': [3, body]}}]
            translated['type_decls'] = [{'def_id': 1, 'item_meta': {'name': type_name}}]
            translated['fun_decls'][0]['item_meta']['name'] = [*type_name[:2], {'Impl': implementation}, {'Ident': ['f', 0]}]
            translated['fun_decls'][0]['body']['Structured']['locals']['locals'][1]['name'] = 'self'
            path = root / 'crate.llbc'
            path.write_text(json.dumps(data))
            inline.check_bindings(root, annotations, path)
            for kind in ('wrong_self', 'missing_self', 'trait', 'cross_module'):
                bad = copy.deepcopy(data)
                translated = bad['translated']
                impl = translated['fun_decls'][0]['item_meta']['name'][2]['Impl']
                if kind == 'wrong_self':
                    translated['type_decls'][0]['item_meta']['name'][-1]['Ident'][0] = 'T'
                elif kind == 'missing_self':
                    impl['Ty']['skip_binder']['Deduplicated'] = 99
                elif kind == 'trait':
                    impl.clear()
                    impl['Trait'] = 0
                else:
                    translated['type_decls'][0]['item_meta']['name'][1]['Ident'][0] = 'other'
                path.write_text(json.dumps(bad))
                with self.subTest(kind=kind), self.assertRaises(ValueError):
                    inline.check_bindings(root, annotations, path)


if __name__ == '__main__':
    unittest.main()
