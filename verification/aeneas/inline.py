#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Account for every inline Aeneas proof and render its checked-in model."""

import argparse
import difflib
import json
import os
import re
import subprocess
from pathlib import Path

import golden

MARKER = re.compile(r'`{2,}\s*([^\s`]+)')
MODEL_SLOT = re.compile(r'@@AENEAS_MODEL\("([^"\n]+)"\)@@')
GOLDEN_SLOT = re.compile(r'@@AENEAS_GOLDEN\("([^"\n]+)"\)@@')


def suspicious(text):
    return any(word.lower().startswith("aeneas") or
               difflib.SequenceMatcher(None, word.lower(), "aeneas").ratio() >= 0.7
               for word in MARKER.findall(text))


def read_source(path):
    return path.read_bytes().decode('utf-8')


def inventory(root):
    data = json.loads((root / 'verification/aeneas/inventory.json').read_text())
    if data['version'] != 1 or not data['functions']:
        raise ValueError('Unsupported or empty Aeneas proof inventory')
    entries = data['functions']
    for key in ('rust', 'model', 'theorem', 'golden'):
        if len({e[key] for e in entries}) != len(entries):
            raise ValueError(f'Duplicate {key} in proof inventory')
    for entry in entries:
        fields = {'rust', 'file', 'syntax', 'model', 'theorem', 'golden'}
        if not fields <= set(entry) or set(entry) - fields - {'depends_on'}:
            raise ValueError('Unknown or missing inventory fields')
        identifier = r'[A-Za-z_][A-Za-z_0-9]*'
        patterns = {'rust': rf'{identifier}(?:::{identifier})*',
                    'syntax': rf'{identifier}(?:::{identifier})*',
                    'model': rf'{identifier}(?:\.{identifier})*', 'theorem': identifier}
        if not all(re.fullmatch(pattern, entry[key]) for key, pattern in patterns.items()):
            raise ValueError('Unsupported declaration identity in inventory')
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*\.lean\.in', entry['golden']):
            raise ValueError('Golden must be a single .lean.in filename')
        if not entry['file'].startswith('zerocopy/src/') or '..' in Path(entry['file']).parts:
            raise ValueError('Only explicit zerocopy source files are supported')
        relative = Path(entry['file']).relative_to('zerocopy/src')
        modules = list(relative.parent.parts)
        if relative.stem not in ('mod', 'lib'):
            modules.append(relative.stem)
        expected_rust = '::'.join(['zerocopy', *modules, entry['syntax']])
        if entry['rust'] != expected_rust:
            raise ValueError('Rust identity must agree with the conventional source module path')
    proof_order(entries)
    return entries


def proof_order(entries):
    """Validate explicit proof edges and order independently of source order."""
    by_rust = {entry['rust']: entry for entry in entries}
    for entry in entries:
        dependencies = entry.get('depends_on', [])
        if (not isinstance(dependencies, list)
                or not all(isinstance(dep, str) for dep in dependencies)
                or len(set(dependencies)) != len(dependencies)):
            raise ValueError(f'{entry["rust"]}: invalid or duplicate proof dependencies')
        missing = set(dependencies) - by_rust.keys()
        if missing:
            raise ValueError(f'{entry["rust"]}: missing proof dependencies: {sorted(missing)}')
    ordered, visiting, visited = [], [], set()

    def visit(rust):
        if rust in visiting:
            cycle = visiting[visiting.index(rust):] + [rust]
            raise ValueError('Cyclic proof dependencies: ' + ' -> '.join(cycle))
        if rust in visited:
            return
        visiting.append(rust)
        for dependency in sorted(by_rust[rust].get('depends_on', [])):
            visit(dependency)
        visiting.pop()
        visited.add(rust)
        ordered.append(by_rust[rust])

    for rust in sorted(by_rust):
        visit(rust)
    return ordered


def source_files(root, entries):
    # Discover across inactive cfg branches and all repository Rust sources,
    # not just the registered files. Only generated/vendor directories are out
    # of scope. A candidate in an unsupported source location is an error.
    paths = {e['file'] for e in entries}
    for directory, dirs, filenames in os.walk(root):
        dirs[:] = [d for d in dirs if d not in {'.git', 'target', 'vendor', '.lake'}]
        for name in filenames:
            if name.endswith('.rs'):
                path = Path(directory) / name
                if suspicious(read_source(path)):
                    paths.add(str(path.relative_to(root)))
    return sorted(paths)


def parse_file(source, syntax):
    # Rust lexer offsets are bytes; Python slices are Unicode code points.
    def char_offset(byte):
        return len(source.encode('utf-8')[:byte].decode('utf-8'))

    comments = [(char_offset(c['start']), char_offset(c['end']))
                for c in syntax['comments']]
    functions = [{**f, 'open': char_offset(f['open']), 'close': char_offset(f['close'])}
                 for f in syntax['functions']]
    found = []
    consumed = set()
    for index, (start, end) in enumerate(comments):
        if index in consumed or not suspicious(source[start:end]):
            continue
        if source[start:end].rstrip() != '// ```aeneas':
            raise ValueError('Malformed, unsupported, or misspelled aeneas fence')
        owners = [f for f in functions if f['supported'] and f['open'] < start
                  and not source[f['open'] + 1:start].strip()]
        if len(owners) != 1:
            raise ValueError('Aeneas fence must be the first non-whitespace token after a function {')
        payload = []
        payload_indices = []
        previous_end = end
        consumed.add(index)
        for following in range(index + 1, len(comments)):
            a, b = comments[following]
            if source[previous_end:a].strip():
                raise ValueError('Aeneas fence must contain consecutive line comments')
            text = source[a:b].rstrip('\r')
            consumed.add(following)
            if text.rstrip() == '// ```':
                break
            if not text.startswith('// ') and text != '//':
                raise ValueError('Aeneas payload requires ordinary // line comments')
            payload.append(text[3:] if text.startswith('// ') else '')
            payload_indices.append((a, b))
            previous_end = b
        else:
            raise ValueError('Unterminated aeneas fence')
        if not payload or payload[0] != 'model:' or payload.count('proof:') != 1:
            raise ValueError('Aeneas fence requires exactly model: then proof:')
        split = payload.index('proof:')
        sections = []
        for lines in (payload[1:split], payload[split + 1:]):
            if not lines or any(line and not line.startswith('  ') for line in lines):
                raise ValueError('Aeneas model/proof content must be indented by two spaces')
            content = '\n'.join(line[2:] if line else '' for line in lines) + '\n'
            normalized = golden.normalize(content)
            if not normalized or any(line and not line[0].isspace() for line in normalized[1:]):
                raise ValueError('Each section must contain exactly one top-level declaration')
            sections.append(content)
        indent = source[source.rfind('\n', 0, start) + 1:start]
        if indent.strip():
            # Allow `{ // fence` but use normal indentation for regenerated lines.
            indent = '    '
        first = payload_indices[1][0]
        last = payload_indices[split][0]
        model_start = source.rfind('\n', 0, first) + 1
        model_end = source.rfind('\n', 0, last) + 1
        found.append({'syntax': owners[0]['path'], 'model_text': sections[0],
                      'proof_text': sections[1], 'model_start': model_start,
                      'model_end': model_end, 'indent': indent,
                      'newline': '\r\n' if '\r\n' in source else '\n',
                      'open_line': source[:owners[0]['open']].count('\n') + 1,
                      'end_line': source[:owners[0]['close']].count('\n') + 1,
                      'end_col': owners[0]['close'] - source.rfind('\n', 0, owners[0]['close']) - 1})
    return found


def discover(root, tool, entries):
    paths = source_files(root, entries)
    result = subprocess.run([str(tool)], cwd=root, input=json.dumps(paths),
                            text=True, capture_output=True)
    if result.returncode:
        raise ValueError(f'Rust syntax inspection failed: {result.stderr}')
    syntax = json.loads(result.stdout)
    annotations = {}
    for file in paths:
        try:
            found = parse_file(read_source(root / file), syntax[file])
        except ValueError as error:
            raise ValueError(f'{file}: {error}') from error
        for annotation in found:
            matches = [e for e in entries if e['file'] == file and e['syntax'] == annotation['syntax']]
            if len(matches) != 1:
                raise ValueError(f'Unregistered annotation in {file}: {annotation["syntax"]}')
            entry = matches[0]
            if entry['rust'] in annotations:
                raise ValueError(f'Duplicate annotation: {entry["rust"]}')
            for section, keyword, name in [('model_text', 'def', entry['model']),
                                           ('proof_text', 'theorem', entry['theorem'])]:
                first = golden.normalize(annotation[section])[0]
                declarations = 'def' if keyword == 'def' else '(?:theorem|contract|partial contract)'
                if not re.match(rf'{declarations} {re.escape(name)}(?=\s|\(|$)', first):
                    raise ValueError(f'{entry["rust"]}: unexpected {keyword} declaration')
            annotations[entry['rust']] = {**entry, **annotation}
    missing = {e['rust'] for e in entries} - annotations.keys()
    if missing:
        raise ValueError(f'Missing inline annotations: {sorted(missing)}')
    return annotations


def templates(root, entries, allow_missing=False):
    directory = root / 'verification/aeneas/golden'
    actual = {str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file()}
    expected = {e['golden'] for e in entries}
    if actual - expected or (not allow_missing and actual != expected):
        raise ValueError(f'Annotation/golden bijection failed: missing={expected - actual}, extra={actual - expected}')
    for entry in entries:
        if allow_missing and not (directory / entry['golden']).exists():
            continue
        text = (directory / entry['golden']).read_text()
        if golden.normalize(text) != [f'@@AENEAS_MODEL("{entry["rust"]}")@@']:
            raise ValueError(f'Golden must contain exactly its registered model slot: {entry["golden"]}')


def render(root, annotations, destination):
    scaffolding = root / 'verification/aeneas/scaffolding'
    actual = {p.name for p in scaffolding.iterdir() if p.is_file()}
    if actual != set(golden.FILES):
        raise ValueError('Unexpected shared Aeneas scaffolding file set')
    by_golden = {a['golden']: a for a in annotations.values()}
    used = []

    def expand(match):
        name = match[1]
        if name not in by_golden:
            raise ValueError(f'Unknown function golden slot: {name}')
        used.append(name)
        return by_golden[name]['model_text'].rstrip('\n')

    destination.mkdir(parents=True, exist_ok=True)
    rendered = {name: GOLDEN_SLOT.sub(expand, (scaffolding / name).read_text())
                for name in golden.FILES}
    if sorted(used) != sorted(by_golden):
        raise ValueError('Every function golden must occur exactly once in scaffolding')
    for name, text in rendered.items():
        if '@@AENEAS_' in text:
            raise ValueError(f'Unexpanded Aeneas slot in {name}')
        (destination / name).write_text(text)


def assemble(root, annotations, work):
    wrapper = (root / 'verification/aeneas/lean/Proofs.lean.in').read_text()
    if wrapper.count('@@AENEAS_PROOFS@@') != 1:
        raise ValueError('Proof wrapper must have exactly one proof slot')
    ordered = proof_order(list(annotations.values()))
    proofs = '\n'.join(a['proof_text'] for a in ordered)
    (work / 'Proofs.lean').write_text(wrapper.replace('@@AENEAS_PROOFS@@', proofs))
    required = ['import Lean', 'import Proofs', 'import Obligations', 'open Lean', '']
    for a in annotations.values():
        # Normalize total WP and scalar order to independently written arithmetic.
        # Layout matchers have different declaration names in the two modules;
        # check both branches explicitly instead of assuming definitional equality.
        name = a['theorem']
        if name == 'pad_to_align_spec':
            body = (f'  unfold Zerocopy.Obligations.{name}\n'
                    '  intro self\n'
                    '  cases hs : self.size_info <;>\n'
                    '    simpa only [hs, Aeneas.Std.WP.spec_equiv_exists] '
                    f'using Zerocopy.Proofs.{name} self')
        else:
            body = (f'  simpa only [Zerocopy.Obligations.{name}, '
                    'Aeneas.Std.WP.spec_equiv_exists, Aeneas.Std.UScalar.eq_equiv, '
                    'Aeneas.Std.UScalar.coe_max, Zerocopy.Arithmetic.coe_min, '
                    'Aeneas.Std.UScalar.lt_equiv, Aeneas.Std.UScalar.le_equiv] '
                    f'using Zerocopy.Proofs.{name}')
        required.append(f'example : Zerocopy.Obligations.{name} := by\n{body}')
    names = ', '.join(f'`Zerocopy.Proofs.{a["theorem"]}' for a in annotations.values())
    required.append(f'def requiredTheorems : Array Name := #[{names}]')
    edges = []
    for a in ordered:
        dependencies = ', '.join(f'`Zerocopy.Proofs.{annotations[dep]["theorem"]}'
                                 for dep in a.get('depends_on', []))
        edges.append(f'(`Zerocopy.Proofs.{a["theorem"]}, #[{dependencies}])')
    required.append('def proofDependencies : Array (Name × Array Name) := #[\n  '
                    + ',\n  '.join(edges) + '\n]')
    (work / 'Required.lean').write_text('\n'.join(required) + '\n')


def check_bindings(root, annotations, llbc):
    # Names alone are insufficient: cfg alternatives can define the same Rust
    # path. Require Charon to have extracted the exact annotated source body.
    translated = json.loads(llbc.read_text())['translated']
    files = {f['id']: f for f in translated['files']}
    # At the pinned Charon version named Self types may be deduplicated. Only
    # collect the Adt type domain, not unrelated Value/Deduplicated domains.
    adts = {}

    def collect_adts(value):
        if isinstance(value, dict):
            if (set(value) == {'Value'} and isinstance(value['Value'], list)
                    and len(value['Value']) == 2 and isinstance(value['Value'][0], int)):
                index, body = value['Value']
                if (isinstance(body, dict) and set(body) == {'Adt'}
                        and isinstance(body['Adt'], dict)
                        and set(body['Adt']) == {'id', 'generics', 'builtin'}):
                    if index in adts and adts[index] != body:
                        raise ValueError('Ambiguous deduplicated Charon Self type')
                    adts[index] = body
            for child in value.values():
                collect_adts(child)
        elif isinstance(value, list):
            for child in value:
                collect_adts(child)

    collect_adts(translated)
    type_names = {t['def_id']: t['item_meta']['name']
                  for t in translated.get('type_decls', []) if t}

    def identifiers(name):
        if not all(set(element) == {'Ident'} and element['Ident'][1] == 0 for element in name):
            raise ValueError('Unsupported extracted root identity')
        return [element['Ident'][0] for element in name]

    def identity(name):
        impls = [i for i, element in enumerate(name) if 'Impl' in element]
        if not impls:
            return '::'.join(identifiers(name))
        if impls != [len(name) - 2]:
            raise ValueError('Unsupported extracted inherent method identity')
        index = impls[0]
        implementation = name[index]['Impl']
        if set(implementation) != {'Ty'}:
            raise ValueError('Trait impl roots are unsupported')
        implementation = implementation['Ty']
        if (implementation['kind'] != 'InherentImplBlock'
                or any(implementation['params'].values())):
            raise ValueError('Generic impl roots are unsupported')
        wrapped = implementation['skip_binder']
        if set(wrapped) == {'Value'}:
            body = wrapped['Value'][1]
        elif set(wrapped) == {'Deduplicated'}:
            body = adts.get(wrapped['Deduplicated'], {})
        else:
            body = {}
        if set(body) != {'Adt'}:
            raise ValueError('Inherent Self must resolve to a named type')
        adt = body['Adt']
        if adt['builtin'] is not None or any(adt['generics'].values()):
            raise ValueError('Generic or builtin Self roots are unsupported')
        self_name = identifiers(type_names.get(adt['id'], []))
        prefix = identifiers(name[:index])
        if not self_name or self_name[:-1] != prefix:
            raise ValueError('Inherent Self must be defined in the annotated module')
        return '::'.join([*self_name, *identifiers(name[index + 1:])])

    roots = {}
    for function in translated['fun_decls']:
        if not function or function['item_meta'].get('started_from') is not True:
            continue
        meta = function['item_meta']
        name = identity(meta['name'])
        if name in roots:
            raise ValueError('Duplicate extracted root identity')
        roots[name] = meta
    if roots.keys() != annotations.keys():
        raise ValueError('Extracted roots do not match the annotated inventory')
    for rust, annotation in annotations.items():
        meta = roots[rust]
        span = meta['span']['Untagged']
        data = span['data']
        file = files[data['file_id']]
        source = read_source(root / annotation['file']).replace('\r\n', '\n')
        if (meta.get('is_local') is not True or span['generated_from_span'] is not None
                or file['name'] != {'Local': annotation['file'].removeprefix('zerocopy/')}
                or file['contents'].replace('\r\n', '\n') != source
                or not data['beg']['line'] <= annotation['open_line'] <= data['end']['line']
                or data['end'] != {'line': annotation['end_line'], 'col': annotation['end_col']}):
            raise ValueError(f'Charon extracted a different source body for {rust}')


def split_live(source, entries):
    # This intentionally supports the pinned generator's root-declaration
    # layout only. Full-file comparison includes all remaining scaffolding;
    # unexpected layouts, missing/duplicate roots or new output fail closed.
    starts = list(re.finditer(r'^/-- \[(zerocopy::[^\]\n]+)\]:\n', source, re.M))

    def identity(display):
        if '{' not in display:
            return display
        match = re.fullmatch(r'(.+::)\{([^{}]+)::([A-Za-z_][A-Za-z_0-9]*)\}::'
                             r'([A-Za-z_][A-Za-z_0-9]*)', display)
        if not match or match[1] != match[2] + '::':
            raise ValueError('Unsupported generated inherent method identity')
        return match[1] + match[3] + '::' + match[4]

    identities = [identity(m[1]) for m in starts]
    if set(identities) != {e['rust'] for e in entries} or len(starts) != len(entries):
        raise ValueError('Pinned Aeneas root declaration layout no longer matches inventory')
    by_rust = {e['rust']: e for e in entries}
    replacements = []
    models = {}
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else source.rfind('\nend Zerocopy')
        # Aeneas ends these documentation comments on the Source: line.
        close = source.find('-/\n', match.start(), end)
        if close < 0 or end < 0:
            raise ValueError('Missing generated root documentation or namespace end')
        declaration_start = close + 3
        model = source[declaration_start:end].rstrip() + '\n'
        rust = identities[index]
        entry = by_rust[rust]
        lines = golden.normalize(model)
        if not lines or not re.match(rf'def {re.escape(entry["model"])}(?=\s|\(|$)', lines[0]):
            raise ValueError('Unexpected generated Lean root identity')
        if any(line and not line[0].isspace() for line in lines[1:]):
            raise ValueError('Unsupported generated root declaration layout')
        models[rust] = model
        replacements.append((declaration_start, end, f'@@AENEAS_GOLDEN("{entry["golden"]}")@@\n\n'))
    for start, end, replacement in reversed(replacements):
        source = source[:start] + replacement + source[end:]
    return models, source


def update(root, entries, annotations, live):
    models, funs = split_live((live / 'Funs.lean').read_text(), entries)
    golden.files(live, live=True)
    changes = {}
    for rust, annotation in annotations.items():
        payload = ''.join(annotation['indent'] + '//   ' + line + annotation['newline']
                          for line in models[rust].splitlines())
        changes.setdefault(annotation['file'], []).append(
            (annotation['model_start'], annotation['model_end'], payload))
    for file, replacements in changes.items():
        path = root / file
        source = read_source(path)
        for start, end, replacement in sorted(replacements, reverse=True):
            source = source[:start] + replacement + source[end:]
        path.write_bytes(source.encode('utf-8'))
    for entry in entries:
        (root / 'verification/aeneas/golden' / entry['golden']).write_text(
            golden.HEADER + f'@@AENEAS_MODEL("{entry["rust"]}")@@\n')
    for name in golden.FILES:
        text = funs if name == 'Funs.lean' else (live / name).read_text()
        (root / 'verification/aeneas/scaffolding' / name).write_text(golden.HEADER + text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['scan', 'scan-update', 'bindings', 'render', 'assemble', 'update'])
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--tool', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    args = parser.parse_args()
    entries = inventory(args.root)
    annotations = discover(args.root, args.tool, entries)
    if args.command == 'bindings':
        check_bindings(args.root, annotations, args.work / 'zerocopy.llbc')
    elif args.command == 'update':
        update(args.root, entries, annotations, args.work)
    elif args.command == 'assemble':
        assemble(args.root, annotations, args.work)
    else:
        templates(args.root, entries, allow_missing=args.command == 'scan-update')
        if args.command in ('scan', 'scan-update'):
            (args.work / 'annotations.json').write_text(json.dumps(annotations, indent=2) + '\n')
            (args.work / 'roots.txt').write_text(','.join(annotations) + '\n')
        elif args.command == 'render':
            render(args.root, annotations, args.work)


if __name__ == '__main__':
    main()
