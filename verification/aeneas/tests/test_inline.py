# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import copy
import json
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
         '    // spec f_spec (x : Nat)\n'
         '    //   ensures r => r = x\n'
         '    // ```\n')
ENTRY = {'file': 'zerocopy/src/util/mod.rs', 'syntax': 'f'}
POLICY = {'version': 2, 'required_functions': [ENTRY], 'covered_impls': []}
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


def fixture(root, source=None, policy=None):
    source = source or 'fn f(x: usize) {\n' + BLOCK + '}\n'
    path = root / ENTRY['file']
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)
    inventory = root / 'verification/aeneas/inventory.json'
    inventory.parent.mkdir(parents=True, exist_ok=True)
    inventory.write_text(json.dumps(policy or POLICY))
    return inline.discover(root, TOOL, policy or POLICY)


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
    def parse(self, source):
        return inline.parse_file(source, syntax(source))

    def test_first_token_crlf_unicode_inactive_cfg_and_source_map(self):
        for eol in ('\n', '\r\n'):
            source = ('const 雪: u8 = 0;\n#[cfg(any())]\nfn f(x: usize) {\n\n' + BLOCK + '}').replace('\n', eol)
            found = self.parse(source)
            self.assertEqual(len(found), 1)
            self.assertEqual(found[0]['syntax'], 'f')
            self.assertEqual(found[0]['spec_text'], 'spec f_spec (x : Nat)\n  ensures r => r = x\n')
            self.assertEqual(found[0]['inputs'], ['x'])
            self.assertEqual(found[0]['source_lines'], [6, 7])
            self.assertEqual(found[0]['newline'], eol)

    def test_rejects_comments_statements_and_nested_scopes_before_fence(self):
        for before in ('// preceding comment\n', '/* preceding */', 'let x = 1;\n',
                       '#[allow(unused)] let x = 1;\n', '{\n'):
            extra_end = '}' if before == '{\n' else ''
            with self.subTest(before=before), self.assertRaises(ValueError):
                self.parse('fn f(x: usize) {\n' + before + BLOCK + extra_end + '}')
        for source in (BLOCK + 'fn f() {}',
                       'fn outer() { fn f(x: usize) {\n' + BLOCK + '} }',
                       'impl Trait for S { fn f(x: usize) {\n' + BLOCK + '} }'):
            with self.assertRaises(ValueError):
                self.parse(source)

    def test_inherent_and_generic_ownership_and_canonical_inputs(self):
        block = BLOCK.replace('(x : Nat)', '{E : Type} (self : S E) (x : Nat)')
        found = self.parse('mod m { impl<E> S<E> { fn f(&self, x: usize) {\n' + block + '} } }')
        self.assertEqual(found[0]['syntax'], 'm::S::f')
        self.assertEqual(found[0]['generics'], ['E'])
        for implementation in ('impl S<u8>', 'impl Trait for S', 'impl m::S'):
            with self.assertRaises(ValueError):
                self.parse(implementation + ' { fn f(x: usize) {\n' + BLOCK + '} }')
        with self.assertRaises(ValueError):
            self.parse('fn f((x, y): (usize, usize)) {\n' + BLOCK + '}')

    def test_binding_prevents_swapped_same_type_inputs_and_missing_generics(self):
        for header in ('(b a : Nat)', '(a : Nat)', '(a a : Nat)', '(other : Nat)'):
            with self.subTest(header=header), self.assertRaises(ValueError):
                self.parse('fn f(a: usize, b: usize) {\n' + BLOCK.replace('(x : Nat)', header) + '}')
        block = BLOCK.replace('(x : Nat)', '(T : Type) (x : T) (ghost : Nat)')
        self.assertEqual(self.parse('fn f<T>(x: T) {\n' + block + '}')[0]['generics'], ['T'])
        with self.assertRaises(ValueError):
            self.parse('fn f<T>(x: T) {\n' + BLOCK + '}')

    def test_requirements_cannot_shadow_inputs_and_parser_frames_are_reserved(self):
        for requirements in ('    //   requires x : True\n',
                             '    //   requires h : True\n    //   requires h : True\n',
                             '    //   aeneas_spec_end\n',
                             '    //     aeneas_spec_begin\n'):
            block = BLOCK.replace('    //   ensures', requirements + '    //   ensures')
            with self.subTest(requirements=requirements), self.assertRaises(ValueError):
                self.parse('fn f(x: usize) {\n' + block + '}')

    def test_closed_and_explicit_coverage_remain_independent_of_discovery(self):
        scope = {'file': ENTRY['file'], 'type': 'S'}
        policy = {'required_functions': [], 'covered_impls': [scope]}
        annotation = {'rust': RUST, 'file': ENTRY['file'], 'syntax': 'S::f'}
        good = syntax('impl<T> S<T> { fn f(self) { fn harness() {} } }')
        inline.check_coverage({RUST: annotation}, {ENTRY['file']: good}, policy)
        for extra in ('fn missing() {}', '#[cfg(any())] fn inactive() {}'):
            bad = syntax('impl S { fn f() {} ' + extra + ' }')
            with self.assertRaisesRegex(ValueError, 'Missing method specification'):
                inline.check_coverage({RUST: annotation}, {ENTRY['file']: bad}, policy)
        with self.assertRaisesRegex(ValueError, 'Missing required function'):
            inline.check_coverage({}, {}, POLICY)
        with self.assertRaisesRegex(ValueError, 'Unsupported impl'):
            inline.check_coverage({RUST: annotation}, {ENTRY['file']: syntax('impl S<u8> { fn f() {} }')}, policy)

    def test_closed_coverage_rejects_macro_and_external_or_qualified_impls(self):
        scope = {'file': ENTRY['file'], 'type': 'S'}
        policy = {'required_functions': [], 'covered_impls': [scope]}
        annotation = {'rust': RUST, 'file': ENTRY['file'], 'syntax': 'S::f'}
        good = 'impl S { fn f() { ordinary!(); } }'
        for extra in ('impl S { methods!(); }',
                      '#[cfg(any())] impl S { #[cfg(any())] methods!(); }'):
            with self.subTest(extra=extra), self.assertRaisesRegex(ValueError, 'Macro in closed coverage impl'):
                inline.check_coverage({RUST: annotation}, {ENTRY['file']: syntax(good + extra)}, policy)
        for extra in ('impl crate::S {}', '#[cfg(any())] impl m::S { fn missed() {} }'):
            with self.subTest(extra=extra), self.assertRaisesRegex(ValueError, 'Unsupported impl'):
                inline.check_coverage({RUST: annotation}, {ENTRY['file']: syntax(good + extra)}, policy)
        external = {ENTRY['file']: syntax(good), 'zerocopy/src/other.rs': syntax('#[cfg(any())] impl S {}')}
        with self.assertRaisesRegex(ValueError, 'Inherent impl outside closed coverage source'):
            inline.check_coverage({RUST: annotation}, external, policy)
        # Unrelated impl-item and body macros retain their normal Rust meaning.
        allowed = syntax(good + 'impl Other { methods!(); } impl Trait for S { methods!(); }')
        inline.check_coverage({RUST: annotation}, {ENTRY['file']: allowed}, policy)

    def test_closed_coverage_discovers_unannotated_impls_and_wildcard_roots(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            policy = {'version': 2, 'required_functions': [],
                      'covered_impls': [{'file': ENTRY['file'], 'type': 'S'}]}
            block = BLOCK.replace('(x : Nat)', '(self : S)')
            annotations = fixture(root, 'impl S { fn f(self) {\n' + block + '} }', policy)
            other = root / 'zerocopy/src/other.rs'
            other.write_text('#[cfg(any())] impl S { fn missed() {} }')
            with self.assertRaisesRegex(ValueError, 'Inherent impl outside closed coverage source'):
                inline.discover(root, TOOL, policy)
            other.write_text('impl Other { methods!(); }')
            self.assertEqual(inline.discover(root, TOOL, policy), annotations)
            work = root / 'work'
            work.mkdir()
            inline.write_scan(annotations, policy, work)
            self.assertEqual((work / 'roots.txt').read_text(), 'zerocopy::util::S::f,zerocopy::util::S::_\n')
            inline.write_scan({RUST: annotation for annotation in annotations.values()}, POLICY, work)
            self.assertEqual((work / 'roots.txt').read_text(), RUST + '\n')

    def test_closed_coverage_rejects_nested_types_missing_from_type_wildcard(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            block = BLOCK.replace('(x : Nat)', '(self : S)')
            source = 'mod m { struct S; impl S { fn f(self) {\n' + block + '} } }'
            policy = {'version': 2, 'required_functions': [],
                      'covered_impls': [{'file': ENTRY['file'], 'type': 'S'}]}
            with self.assertRaisesRegex(ValueError, 'Nested impl in closed coverage scope'):
                fixture(root, source, policy)
            # Explicit function coverage still supports nested module paths.
            explicit = {'version': 2, 'required_functions': [{**ENTRY, 'syntax': 'm::S::f'}],
                        'covered_impls': []}
            self.assertEqual(set(fixture(root, source, explicit)), {'zerocopy::util::m::S::f'})
            top_level = 'struct S; impl S { fn f(self) {\n' + block + '} }'
            with self.assertRaisesRegex(ValueError, 'Nested impl in closed coverage scope'):
                fixture(root, top_level + '#[cfg(any())] mod m { impl S {} }', policy)

    def test_coverage_policy_rejects_derived_bookkeeping_and_duplicates(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root)
            path = root / 'verification/aeneas/inventory.json'
            self.assertEqual(inline.inventory(root), POLICY)
            for invalid in ({**POLICY, 'functions': []},
                            {**POLICY, 'version': 1},
                            {**POLICY, 'required_functions': [ENTRY, ENTRY]},
                            {**POLICY, 'required_functions': [], 'covered_impls': []},
                            {**POLICY, 'required_functions': [{**ENTRY, 'file': 'zerocopy/src/../outside.rs'}]}):
                path.write_text(json.dumps(invalid))
                with self.subTest(policy=invalid), self.assertRaises(ValueError):
                    inline.inventory(root)

    def test_rejects_near_miss_guards_legacy_sections_and_extra_commands(self):
        variants = [BLOCK.replace('```aeneas', guard) for guard in
                    ('```Aeneas', '```aeneos', '``aeneas', '```aeneas v2')]
        variants += [BLOCK.replace('// ```aeneas', '/// ```aeneas'),
                     BLOCK.replace('    // ```\n', ''),
                     BLOCK.replace('    // ```\n', '    // ``` trailing\n'),
                     BLOCK.replace('    //   ensures', '    let x = 1;\n    //   ensures'),
                     BLOCK.replace('    //   ensures', '    // ensures'),
                     BLOCK.replace('    //   ensures', '    //   for util.other x\n    //   ensures'),
                     BLOCK.replace('    //   ensures', '    //   proof:\n    //   ensures'),
                     BLOCK.replace('    // spec', '    // model:\n    // spec'),
                     BLOCK.replace('    // ```\n', '    // def extra := 1\n    // ```\n')]
        for block in variants:
            with self.subTest(block=block), self.assertRaises(ValueError):
                self.parse('fn f(x: usize) {\n' + block + '}')

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
            with self.assertRaisesRegex(ValueError, 'Missing required function'):
                inline.discover(root, TOOL, POLICY)
            fixture(root)
            path.write_text(path.read_text() * 2)
            with self.assertRaisesRegex(ValueError, 'Duplicate annotation'):
                inline.discover(root, TOOL, POLICY)
            fixture(root)
            (root / 'unsupported.rs').write_text('fn f(x: usize) {\n' + BLOCK + '}')
            with self.assertRaisesRegex(ValueError, 'Unsupported annotated'):
                inline.discover(root, TOOL, POLICY)

    def test_models_derive_root_names_and_verify_parameter_order(self):
        annotations = {RUST: {'generics': [], 'inputs': ['x']}}
        self.assertEqual(inline.generated_bindings(GENERATED, annotations), {RUST: 'util.f'})
        for bad in (GENERATED.replace('(x : Nat)', '(other : Nat)'),
                    GENERATED.replace('[zerocopy::util::f]', '[zerocopy::util::other]'),
                    GENERATED.replace('\nend Zerocopy', GENERATED + '\nend Zerocopy')):
            with self.assertRaises(ValueError):
                inline.generated_bindings(bad, annotations)
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
            self.assertIn('spec f_spec (x : Nat)\n  for @Zerocopy.util.f x\n  ensures', specs)
            required = (work / 'Required.lean').read_text()
            self.assertIn('example : Zerocopy.Specs.f_spec := @Zerocopy.Proofs.f_spec', required)
            self.assertIn('check_contract Zerocopy.Obligations.f_spec using @Zerocopy.Proofs.f_spec', required)
            self.assertIn('proofModuleNames : Array Name := #[`Proofs, `Proofs.Util]', required)
            self.assertIn('import ExtraFacts', required)
            self.assertIn('auditModuleNames : Array Name := #[`ExtraFacts', required)
            mapping = json.loads((work / 'Specs.source-map.json').read_text())
            for index, line in enumerate(specs.splitlines(), 1):
                if line.startswith('spec '):
                    self.assertEqual(mapping[str(index)], {'file': ENTRY['file'], 'line': 3})
                if line.startswith('  for '):
                    self.assertEqual(mapping[str(index)], {'file': ENTRY['file'], 'line': 3})
                if line.startswith('  ensures '):
                    self.assertEqual(mapping[str(index)], {'file': ENTRY['file'], 'line': 4})
            # Comment-only golden variation is allowed, but code and source
            # changes invalidate the mapping before any proof is compiled.
            (work / 'Zerocopy/Funs.lean').write_text('-- moved\n' + GENERATED)
            inline.assemble(root, annotations, work)
            (work / 'Zerocopy/Funs.lean').write_text(GENERATED.replace('x + 1', 'x + 2'))
            with self.assertRaisesRegex(ValueError, 'stale'):
                inline.assemble(root, annotations, work)
            (work / 'Zerocopy/Funs.lean').write_text(GENERATED)
            (root / ENTRY['file']).write_text((root / ENTRY['file']).read_text() + '// changed\n')
            with self.assertRaisesRegex(ValueError, 'stale'):
                inline.assemble(root, annotations, work)

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

    def test_closed_wildcard_roster_ignores_constant_initializers_but_not_methods(self):
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
            inline.check_bindings(root, annotations, path)
            initializer['src'] = 'Normal'
            initializer['item_meta']['name'][-1]['Ident'][0] = 'generated_method'
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'Extracted roots do not match'):
                inline.check_bindings(root, annotations, path)

    def test_inherent_method_llbc_identity_resolves_named_self(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            block = BLOCK.replace('(x : Nat)', '(self : S)')
            source = 'struct S; impl S { fn f(self) {\n' + block + '} }\n'
            policy = {'version': 2, 'required_functions': [], 'covered_impls': [{'file': ENTRY['file'], 'type': 'S'}]}
            annotations = fixture(root, source, policy)
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
