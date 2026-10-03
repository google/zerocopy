#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Discover Rust specifications and generate their independently checked Lean goals."""

import argparse
import difflib
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

import golden
import workspace

MARKER = re.compile(r'`{2,}\s*([^\s`]+)')
IDENTIFIER = r'[A-Za-z_][A-Za-z_0-9]*'


class Annotations(dict):
    """Discovered declarations plus generated source nominal metadata."""

    def __init__(self):
        super().__init__()
        self.types = []
        self.extracted_types = None


def suspicious(text):
    return any(word.lower().startswith('aeneas') or
               difflib.SequenceMatcher(None, word.lower(), 'aeneas').ratio() >= 0.7
               for word in MARKER.findall(text))


def read_source(path):
    return path.read_bytes().decode('utf-8')


def rust_identity(file, syntax):
    relative = Path(file).relative_to('zerocopy/src')
    modules = list(relative.parent.parts)
    if relative.stem not in ('mod', 'lib'):
        modules.append(relative.stem)
    return '::'.join(['zerocopy', *modules, syntax])


def valid_file(file):
    return (isinstance(file, str) and file.startswith('zerocopy/src/')
            and '..' not in Path(file).parts and file.endswith('.rs'))


def inventory(root):
    data = json.loads((root / 'verification/aeneas/inventory.json').read_text())
    if set(data) - {'license', 'version', 'required_functions', 'covered_impls'} or data['version'] != 2:
        raise ValueError('Unsupported Aeneas coverage policy')
    scopes = data.get('covered_impls', [])
    required = data.get('required_functions', [])
    for entries, key in ((scopes, 'type'), (required, 'syntax')):
        if (not isinstance(entries, list)
                or any(not isinstance(entry, dict) or set(entry) != {'file', key}
                       or not valid_file(entry['file']) or not isinstance(entry[key], str)
                       or not re.fullmatch(IDENTIFIER + (r'(?:::' + IDENTIFIER + ')*' if key == 'syntax' else ''), entry[key])
                       for entry in entries)
                or len({(entry['file'], entry[key]) for entry in entries}) != len(entries)):
            raise ValueError(f'Invalid or duplicate coverage {key}')
    if not scopes and not required:
        raise ValueError('Aeneas coverage policy must require at least one function or impl')
    return data


def source_files(root, policy):
    # Inspect inactive cfg branches and all repository Rust sources. Literal
    # lookalikes are filtered by the Rust lexer, not by this discovery heuristic.
    paths = {entry['file'] for kind in ('required_functions', 'covered_impls')
             for entry in policy.get(kind, [])}
    for directory, dirs, filenames in os.walk(root):
        dirs[:] = [d for d in dirs if d not in {'.git', 'target', 'vendor', '.lake'}]
        for name in filenames:
            if name.endswith('.rs'):
                path = Path(directory) / name
                relative = str(path.relative_to(root))
                # Inherent impls can be added in another source file without an
                # annotation. Closed type coverage must inspect those files too.
                if (relative.startswith('zerocopy/src/')
                        or suspicious(read_source(path))):
                    paths.add(relative)
    return sorted(paths)


def binder_header(text, position):
    """Read our deliberately small named-binder subset; Lean checks the types."""
    names = []
    pairs = {'(': ')', '{': '}', '[': ']'}
    while True:
        while position < len(text) and text[position].isspace():
            position += 1
        if position == len(text) or text[position] not in pairs:
            return names, position
        start = position
        stack = [pairs[text[position]]]
        position += 1
        literal = None
        while stack:
            if position == len(text):
                raise ValueError('Unterminated specification binder')
            char = text[position]
            if literal:
                if char == '\\' and literal == '"':
                    position += 2
                    continue
                if char == literal:
                    literal = None
            elif char in ('"', '«'):
                literal = '"' if char == '"' else '»'
            elif char in pairs:
                stack.append(pairs[char])
            elif char in pairs.values():
                if char != stack.pop():
                    raise ValueError('Mismatched specification binder')
            position += 1
        declaration = text[start + 1:position - 1]
        before_type, separator, _ = declaration.partition(':')
        if not separator or not re.fullmatch(IDENTIFIER + r'(?:\s+' + IDENTIFIER + ')*', before_type.strip()):
            raise ValueError('Specification binders must have explicit names and types')
        names.extend(before_type.split())


def parse_spec(text, generics, inputs):
    normalized = '\n'.join(golden.normalize(text))
    if re.search(r'\baeneas_spec_(?:begin|end)\b', text):
        raise ValueError('Specification parser framing markers are reserved for generated Lean')
    match = re.match(r'^(?:partial )?spec (' + IDENTIFIER + r')(?=\s|\(|\{|$)', normalized)
    if not match:
        raise ValueError('Aeneas fence requires exactly one spec declaration')
    names, body = binder_header(normalized, match.end())
    if len(set(names)) != len(names):
        raise ValueError('Duplicate specification binder')
    expected = generics + inputs
    if set(names) & set(expected):
        raise ValueError('Ghost binders must not shadow original Rust parameters')
    if not re.match(r'(?:requires|refines|ensures)\b', normalized[body:]):
        raise ValueError('Specification requires a postcondition; for applications and proof bodies are generated externally')
    # Every continuation is indented. This excludes additional top-level Lean
    # declarations, commands and legacy model/proof sections inside the fence.
    if any(line and not line.startswith('  ') for line in text.splitlines()[1:]):
        raise ValueError('Specification continuations must be indented by two spaces')
    if re.search(r'^\s*(?:for|proof:|model:|contract|theorem|def|abbrev|spec)\b', normalized[body:], re.M):
        raise ValueError('Aeneas fence contains an unsupported application or declaration')
    requirements = re.findall(r'^\s*requires\s+(' + IDENTIFIER + r')\s*:', normalized[body:], re.M)
    if len(set(requirements)) != len(requirements) or set(requirements) & set(names + expected):
        raise ValueError('Requirement names must be unique and must not shadow specification binders')
    # Insertion uses the original text, preserving exact line mappings and term
    # contents. The first clause starts on a new line after the named binders.
    _, original_body = binder_header(text, re.match(r'^(?:partial )?spec\s+' + IDENTIFIER, text).end())
    clause_line = text[:original_body].count('\n')
    if clause_line == 0 or text[:original_body].rsplit('\n', 1)[1].strip():
        raise ValueError('Specification clauses must begin on their own indented lines')
    return match[1], clause_line


def parse_invariant(text, generics):
    normalized = '\n'.join(golden.normalize(text))
    match = re.match(r'^invariant (' + IDENTIFIER + r')\s+for\s+(' + IDENTIFIER + r')\s*=>\s*(.+)$', normalized, re.S)
    if not match or re.search(r'\baeneas_(?:spec|invariant)_(?:begin|end)\b', text):
        raise ValueError('Aeneas type fence requires exactly one invariant name for value => predicate declaration')
    if match[2] in generics:
        raise ValueError('Invariant value must not shadow a Rust type parameter')
    if any(line and not line.startswith('  ') for line in text.splitlines()[1:]):
        raise ValueError('Invariant continuations must be indented by two spaces')
    if re.search(r'^\s*(?:for|spec|partial|invariant|theorem|def|abbrev|proof:|model:)\b', match[3], re.M):
        raise ValueError('Aeneas fence contains an unsupported application or declaration')
    # Keep the authored predicate rather than normalized terms, for source maps.
    authored = re.match(r'^invariant\s+' + IDENTIFIER + r'\s+for\s+' + IDENTIFIER + r'\s*=>\s*', text)
    return match[1], match[2], text[authored.end():].rstrip('\n'), text[:authored.end()].count('\n')


def parse_file(source, syntax):
    def char_offset(byte):
        return len(source.encode('utf-8')[:byte].decode('utf-8'))

    found, owned = [], set()
    owners = [*syntax['functions'], *syntax.get('types', [])]
    for owner in owners:
        if owner.get('include_str_docs'):
            raise ValueError('Direct include_str! in owner doc expressions is unsupported; use literal outer docs')
        docs = owner.get('docs', [])
        if owner.get('computed_docs') and any(suspicious(doc['text']) for doc in docs):
            raise ValueError('Computed doc strings on function or nominal type owners are unsupported; use literal outer docs')
        content, lines = [], []
        for doc in docs:
            owned.add((doc['start'], doc['end']))
            # /// desugars to a string beginning with one conventional space.
            # Literal #[doc = "..."] uses the same decoded Rust string semantics.
            decoded = doc['text'].splitlines() or ['']
            raw_doc = source[char_offset(doc['start']):char_offset(doc['end'])]
            block_stars = raw_doc.startswith('/**') and all(
                not line.strip() or re.match(r'^\s*\*(?: |$)', line) for line in decoded)
            for index, line in enumerate(decoded):
                if block_stars:
                    line = re.sub(r'^\s*\*(?: |$)', '', line)
                elif (raw_doc.startswith('///') or (raw_doc.startswith('/**') and index == 0)) and line.startswith(' '):
                    line = line[1:]
                content.append(line)
                lines.append(doc['line'] + index if source[char_offset(doc['start']):].startswith(('///', '/**')) else doc['line'])
        index, count = 0, 0
        while index < len(content):
            line = content[index]
            if not suspicious(line):
                index += 1
                continue
            if line.rstrip() != '```aeneas':
                raise ValueError('Malformed, unsupported, or misspelled aeneas fence')
            if not owner['supported']:
                raise ValueError('Aeneas fence has an unsupported Rust owner (including borrowed/backward forms)')
            count += 1
            if count != 1:
                raise ValueError('Duplicate Aeneas declarations on one Rust owner')
            start = index + 1
            index = start
            while index < len(content) and content[index].rstrip() != '```':
                if suspicious(content[index]) or content[index].startswith('```'):
                    raise ValueError('Malformed or nested aeneas fence')
                index += 1
            if index == len(content):
                raise ValueError('Unterminated aeneas fence')
            payload = '\n'.join(content[start:index]) + '\n'
            kind = 'function' if owner.get('kind', 'function') == 'function' else 'type'
            if kind == 'function':
                name, clause_line = parse_spec(payload, owner['generics'], owner['inputs'])
                extra = {'spec_text': payload, 'clause_line': clause_line,
                         'ghosts': binder_header(payload, re.match(r'^(?:partial )?spec\s+' + IDENTIFIER, payload).end())[0]}
            else:
                name, binder, predicate, predicate_line = parse_invariant(payload, owner['generics'])
                extra = {'invariant_text': payload, 'value_binder': binder,
                         'nominal_kind': owner['kind'], 'fields': owner['fields'],
                         'predicate_text': predicate, 'predicate_line': predicate_line}
            close = char_offset(owner['close'])
            declaration = char_offset(owner['start'])
            found.append({'syntax': owner['path'], 'kind': kind, 'theorem': name,
                          'generics': owner['generics'], 'inputs': owner['inputs'],
                          'source_lines': lines[start:index],
                          'newline': '\r\n' if '\r\n' in source else '\n',
                          'open_line': source[:declaration].count('\n') + 1,
                          'end_line': source[:close].count('\n') + 1,
                          'end_col': close - source.rfind('\n', 0, close) - 1,
                          **extra})
            index += 1
    # The AST's ownership relation is authoritative. Audit the lexer and every
    # doc spelling so an unsupported/orphaned reserved fence cannot disappear.
    for attr in syntax.get('attributes', []):
        span = (attr['start'], attr['end'])
        raw = source[char_offset(span[0]):char_offset(span[1])]
        if (suspicious(raw) or suspicious(''.join(attr.get('fragments', [])))) and span not in owned:
            raise ValueError('Reserved aeneas fence in unsupported, conditional, computed, inner, or orphaned doc attribute')
    for comment in syntax['comments']:
        span = (comment['start'], comment['end'])
        raw = source[char_offset(span[0]):char_offset(span[1])]
        if suspicious(raw) and not any(a <= span[0] and span[1] <= b for a, b in owned):
            raise ValueError('Reserved aeneas fence must belong to an outer Rust doc attribute on a supported function or nominal type')
    return found


def check_coverage(annotations, syntax, policy):
    for entry in policy.get('required_functions', []):
        matches = [a for a in annotations.values() if a.get('kind', 'function') == 'function' and a['file'] == entry['file'] and a['syntax'] == entry['syntax']]
        if len(matches) != 1:
            raise ValueError(f'Missing required function specification: {entry}')
    for scope in policy.get('covered_impls', []):
        for file, inspected in syntax.items():
            for implementation in inspected['implementations']:
                if not implementation['inherent'] or implementation['type'] != scope['type']:
                    continue
                if file != scope['file']:
                    raise ValueError(f'Inherent impl outside closed coverage source: {scope["type"]} in {file}')
                if not implementation['supported']:
                    raise ValueError(f'Unsupported impl in closed coverage scope: {scope["type"]}')
                # Policy types name the source file's top-level type. A nested
                # same-named type has a different Charon wildcard identity;
                # accepting it here would leave its expanded methods unchecked.
                if implementation['modules']:
                    raise ValueError(f'Nested impl in closed coverage scope: {scope["type"]}')
                if implementation['macros']:
                    raise ValueError(f'Macro in closed coverage impl: {scope["type"]}: {implementation["macros"]}')
        methods = [f for f in syntax[scope['file']]['functions']
                   if f['method'] and f['inherent'] and f['impl_type'] == scope['type']]
        if not methods:
            raise ValueError(f'Closed coverage scope has no methods: {scope}')
        for function in methods:
            if not function['supported']:
                raise ValueError(f'Unsupported method in closed coverage scope: {function["path"]}')
            matches = [a for a in annotations.values() if a.get('kind', 'function') == 'function' and a['file'] == scope['file'] and a['syntax'] == function['path']]
            if len(matches) != 1:
                raise ValueError(f'Missing method specification in closed coverage scope: {function["path"]}')


def write_scan(annotations, policy, work):
    # Charon's named-Self subitem pattern selects inherent methods regardless
    # of the impl's module, including macro-generated and aliased methods. The
    # exact started_from roster check then catches methods invisible to syn.
    roots = [*annotations, *(rust_identity(scope['file'], scope['type']) + '::_'
                             for scope in policy.get('covered_impls', []))]
    (work / 'annotations.json').write_text(json.dumps(annotations, indent=2) + '\n')
    (work / 'source-types.json').write_text(json.dumps(getattr(annotations, 'types', []), indent=2) + '\n')
    (work / 'roots.txt').write_text(','.join(roots) + '\n')


def discover(root, tool, policy):
    paths = source_files(root, policy)
    result = subprocess.run([str(tool)], cwd=root, input=json.dumps(paths), text=True, capture_output=True)
    if result.returncode:
        raise ValueError(f'Rust syntax inspection failed: {result.stderr}')
    syntax = json.loads(result.stdout)
    annotations = Annotations()
    for file in paths:
        try:
            found = parse_file(read_source(root / file), syntax[file])
        except ValueError as error:
            raise ValueError(f'{file}: {error}') from error
        if valid_file(file):
            source = read_source(root / file)
            encoded = source.encode('utf-8')
            for owner in syntax[file].get('types', []):
                start = len(encoded[:owner['start']].decode('utf-8'))
                close = len(encoded[:owner['close']].decode('utf-8'))
                annotations.types.append({
                    'rust': rust_identity(file, owner['path']), 'file': file,
                    'syntax': owner['path'], 'kind': 'type', 'nominal_kind': owner['kind'],
                    'generics': owner['generics'], 'inputs': [], 'supported': owner['supported'],
                    'fields': owner['fields'], 'open_line': source[:start].count('\n') + 1,
                    'end_line': source[:close].count('\n') + 1,
                    'end_col': close - source.rfind('\n', 0, close) - 1})
        for annotation in found:
            if not valid_file(file):
                raise ValueError(f'Unsupported annotated source location: {file}')
            rust = rust_identity(file, annotation['syntax'])
            if rust in annotations:
                raise ValueError(f'Duplicate annotation: {rust}')
            if annotation['theorem'] in {a['theorem'] for a in annotations.values()}:
                raise ValueError(f'Duplicate specification name: {annotation["theorem"]}')
            annotations[rust] = {**annotation, 'rust': rust, 'file': file}
    check_coverage(annotations, syntax, policy)
    if not annotations:
        raise ValueError('No Aeneas specifications discovered')
    return annotations


def check_goldens(root, allow_missing=False):
    directory = root / 'verification/aeneas/golden'
    if allow_missing:
        actual = {str(path.relative_to(directory)) for path in directory.rglob('*') if path.is_file()}
        if actual <= set(golden.FILES):
            return
    golden.files(directory)


def render(root, destination):
    generated = golden.files(root / 'verification/aeneas/golden')
    destination.mkdir(parents=True, exist_ok=True)
    for name, text in generated.items():
        (destination / name).write_text(text)


def generated_nominal_types(source):
    """Read local nominal declarations in Aeneas's extracted dependency order."""
    starts = list(re.finditer(r'^/-- \[(zerocopy::[^\]\n]+)\][^\n]*\n', source, re.M))
    result, seen = [], set()
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else source.rfind('\nend Zerocopy')
        close = source.find('-/\n', match.start(), end)
        if close < 0 or end < 0:
            raise ValueError('Missing generated type documentation or namespace end')
        declaration = source[close + 3:end]
        declaration = re.sub(r'^(?:@\[[^\]\n]*\]\n)+', '', declaration)
        header = re.match(r'(structure|inductive) (' + IDENTIFIER + r'(?:\.' + IDENTIFIER + r')*)\b', declaration)
        if not header:
            # Genuine aliases are normalized to their existing carriers. In
            # particular they never receive a competing validity instance.
            if re.match(r'(?:def|abbrev)\s', declaration):
                continue
            raise ValueError(f'Unsupported generated type declaration: {match[1]}')
        if match[1] in seen:
            raise ValueError(f'Duplicate generated Lean type identity: {match[1]}')
        seen.add(match[1])
        names, _ = binder_header(declaration, header.end())
        result.append({'rust': match[1], 'model': header[2], 'generics': names,
                       'nominal_kind': 'struct' if header[1] == 'structure' else 'enum'})
    return result


def generated_bindings(source, annotations, types_source=None):
    """Associate root definitions with pinned Aeneas Rust identity metadata."""
    starts = list(re.finditer(r'^/-- [^\n]*\n', source, re.M))
    models = {}
    for index, match in enumerate(starts):
        display = re.match(r'/-- \[(zerocopy::[^\]\n]+)\]:', match[0])
        if not display:
            continue
        rust = display[1]
        if '{' in rust:
            method = re.fullmatch(r'(.+::)\{([^{}]+)::(' + IDENTIFIER + r')(?:<[^{}]+>)?\}::(' + IDENTIFIER + ')', rust)
            if not method or method[1] != method[2] + '::':
                raise ValueError('Unsupported generated inherent method identity')
            rust = method[1] + method[3] + '::' + method[4]
        if (rust not in annotations or annotations[rust].get('kind', 'function') != 'function'
                or re.search(r': loop(?: body)? \d+:', match[0])):
            continue
        end = starts[index + 1].start() if index + 1 < len(starts) else source.rfind('\nend Zerocopy')
        close = source.find('-/\n', match.start(), end)
        if close < 0 or end < 0:
            raise ValueError('Missing generated root documentation or namespace end')
        declaration = source[close + 3:end]
        header = re.match(r'def (' + IDENTIFIER + r'(?:\.' + IDENTIFIER + r')*)\b', declaration)
        if not header:
            raise ValueError(f'Unsupported generated root declaration for {rust}')
        if rust in models:
            raise ValueError(f'Duplicate generated Lean root identity: {rust}')
        names, _ = binder_header(declaration, header.end())
        expected = annotations[rust]['generics'] + annotations[rust]['inputs']
        if names != expected:
            raise ValueError(f'Generated model parameters disagree with Rust parameters for {rust}: {names} != {expected}')
        models[rust] = header[1]
    type_annotations = {rust: a for rust, a in annotations.items() if a.get('kind') == 'type'}
    if type_annotations:
        if types_source is None:
            raise ValueError('Generated Types.lean is required to bind type invariants')
        for declaration in generated_nominal_types(types_source):
            rust = declaration['rust']
            if rust not in type_annotations:
                continue
            annotation = type_annotations[rust]
            if declaration['nominal_kind'] != annotation['nominal_kind']:
                raise ValueError(f'Generated type kind disagrees with Rust owner: {rust}')
            if declaration['generics'] != annotation['generics']:
                raise ValueError(f'Generated model type parameters disagree with Rust parameters for {rust}')
            models[rust] = declaration['model']
    if models.keys() != annotations.keys():
        raise ValueError('Generated Lean root declarations do not match discovered specifications')
    return models


def source_digest(root, annotations):
    digest = hashlib.sha256()
    paths = {'verification/aeneas/inventory.json', *(a['file'] for a in annotations.values()),
             *(a['file'] for a in getattr(annotations, 'types', []))}
    for file in sorted(paths):
        digest.update(file.encode())
        digest.update((root / file).read_bytes())
    return digest.hexdigest()


def model_digest(work):
    normalized = '\n'.join(golden.normalize((work / 'Zerocopy/Funs.lean').read_text()))
    types = work / 'Zerocopy/Types.lean'
    if types.exists():
        normalized += '\n' + '\n'.join(golden.normalize(types.read_text()))
    return hashlib.sha256(normalized.encode()).hexdigest()


def save_bindings(root, annotations, work, development=False):
    types = work / 'Zerocopy/Types.lean'
    models = generated_bindings((work / 'Zerocopy/Funs.lean').read_text(), annotations,
                                types.read_text() if types.exists() else None)
    nominal = generated_nominal_types(types.read_text()) if types.exists() else []
    source_types = getattr(annotations, 'extracted_types', None)
    if source_types is None:
        source_types = {}
        for source in getattr(annotations, 'types', []):
            source_types.setdefault(source['rust'], []).append(source)
    if getattr(annotations, 'extracted_types', None) is not None:
        if {declaration['rust'] for declaration in nominal} != set(source_types):
            raise ValueError('Generated nominal type declarations do not match extracted Rust nominal types')
    for declaration in nominal:
        candidates = source_types.get(declaration['rust'], [])
        if isinstance(candidates, dict):
            candidates = [candidates]
        if len(candidates) != 1:
            raise ValueError(f'Generated nominal type lacks unambiguous verified source ownership: {declaration["rust"]}')
        source = candidates[0]
        if (not source['supported'] or declaration['generics'] != source['generics']
                or declaration['nominal_kind'] != source['nominal_kind']):
            raise ValueError(f'Generated nominal type disagrees with supported Rust source: {declaration["rust"]}')
    manifest = {'version': 2, 'types': nominal,
                'invariants': {a['rust']: a['theorem'] for a in annotations.values() if a.get('kind') == 'type'}, 'mode': 'development' if development else 'verified-live',
                'sources': source_digest(root, annotations), 'model': model_digest(work), 'models': models}
    (work / 'bindings.json').write_text(json.dumps(manifest, indent=2) + '\n')


def assemble(root, annotations, work, development=False):
    if not (root / 'verification/aeneas/lean/RequiredContracts.lean').is_file():
        raise ValueError('RequiredContracts.lean is required for independent specification checks')
    # CI saves this mapping only after exact-body Charon checks and live Aeneas
    # generation. The golden build consumes that same mapping, never its docs.
    saved = work / 'bindings.json'
    if not saved.exists():
        raise ValueError('Verified live model bindings are required before specification generation')
    manifest = json.loads(saved.read_text())
    expected_mode = 'development' if development else 'verified-live'
    if (manifest.get('version') != 2 or manifest.get('mode') != expected_mode
            or manifest.get('sources') != source_digest(root, annotations)
            or manifest.get('model') != model_digest(work)):
        raise ValueError('Model bindings are stale; regenerate specs from the current sources and model')
    bindings = manifest['models']
    if set(bindings) != set(annotations):
        raise ValueError('Verified live bindings do not cover every specification')
    imports = ['module', 'public import Zerocopy.Funs', 'public import SpecPrelude', 'public import SpecsSyntax', 'public import Invariants', 'public import ValidityFallback']
    if (root / 'verification/aeneas/lean/LayoutModel.lean').exists():
        imports.append('public import LayoutModel')
    elif (root / 'verification/aeneas/lean/Arithmetic.lean').exists():
        imports.append('public import Arithmetic')
    specs = [*golden.HEADER.rstrip().splitlines(), '', *imports, '@[expose] public section', '',
             'open Aeneas Aeneas.Std', 'open Zerocopy.Proofs', 'namespace Zerocopy.Specs', '']
    source_map = {}
    for a in annotations.values():
        if a.get('kind', 'function') != 'function':
            continue
        model = bindings[a['rust']]
        if not re.fullmatch(IDENTIFIER + r'(?:\.' + IDENTIFIER + ')*', model):
            raise ValueError('Invalid verified generated model name')
        lines = a['spec_text'].rstrip('\n').split('\n')
        clause = a['clause_line']
        application = f'@Zerocopy.{model} with {len(a["generics"])} type parameters'
        lines.insert(clause, '  for ' + application)
        source_map[str(len(specs) + 1)] = {'file': a['file'], 'line': a['source_lines'][0]}
        specs.append(f'check_model_validity_inputs Zerocopy.{model} with {len(a["generics"])} type parameters')
        specs.append('aeneas_spec_begin')
        for index, line in enumerate(lines):
            original = max(0, index - (index >= clause))
            source_map[str(len(specs) + 1)] = {'file': a['file'], 'line': a['source_lines'][original]}
            specs.append(line)
        source_map[str(len(specs) + 1)] = {'file': a['file'], 'line': a['source_lines'][-1]}
        specs.append('aeneas_spec_end')
        source_map[str(len(specs) + 1)] = {'file': a['file'], 'line': a['source_lines'][0]}
        specs.append(f'check_spec_binding Zerocopy.Specs.{a["theorem"]} '
                     f'for Zerocopy.{model} with {len(a["generics"]) + len(a["inputs"])}')
        specs.append('')
    specs.extend(['end Zerocopy.Specs', ''])
    (work / 'Specs.lean').write_text('\n'.join(specs))
    (work / 'Specs.source-map.json').write_text(json.dumps(source_map, indent=2) + '\n')
    invariants = [*golden.HEADER.rstrip().splitlines(), '', 'module',
                  'public import Zerocopy.Types', 'public import SpecPrelude',
                  'public import DeriveValidity', 'public import ValidityNative',
                  '@[expose] public section', '',
                  'open Aeneas Aeneas.Std', 'namespace Zerocopy.Invariants', '']
    invariant_map = {}
    # Preserve extracted type declaration order, already verified by the binding
    # parser; structural instances use the model environment's same order.
    for declaration in manifest['types']:
        rust, model = declaration['rust'], declaration['model']
        count = len(declaration['generics'])
        a = annotations.get(rust)
        if a and a.get('kind') == 'type':
            invariant_map[str(len(invariants) + 1)] = {'file': a['file'], 'line': a['source_lines'][0]}
            invariants.append('aeneas_invariant_begin')
            invariants.append(f'aeneas_invariant {a["theorem"]} for Zerocopy.{model} '
                              f'with {count} type parameters :=')
            for index, line in enumerate(('fun ' + a['value_binder'] + ' => ' + a['predicate_text']).splitlines()):
                invariant_map[str(len(invariants) + 1)] = {'file': a['file'],
                    'line': a['source_lines'][min(a['predicate_line'] + index, len(a['source_lines']) - 1)]}
                invariants.append('  ' + line)
            invariants.append('aeneas_invariant_end')
        invariants.append(f'derive_model_validity Zerocopy.{model} with {count} type parameters')
        if a and a.get('kind') == 'type':
            invariants.append(f'check_invariant_binding Zerocopy.Invariants.{a["theorem"]} '
                              f'for Zerocopy.{model} with {count} type parameters')
        invariants.append('')
    invariants.extend(['end Zerocopy.Invariants', ''])
    (work / 'Invariants.lean').write_text('\n'.join(invariants))
    (work / 'Invariants.source-map.json').write_text(json.dumps(invariant_map, indent=2) + '\n')
    modules = ['Proofs', *sorted(str(path.relative_to(root / 'verification/aeneas/lean')).removesuffix('.lean').replace('/', '.')
                               for path in (root / 'verification/aeneas/lean/Proofs').rglob('*.lean'))]
    # Import every configured native proof module, even when its declarations
    # are unused by the aggregate. Otherwise a private helper could evade the
    # axiom audit simply by being omitted from the aggregate's imports.
    audit_modules = sorted({'Specs', 'Invariants', 'Zerocopy.Funs', 'Zerocopy.Types',
                            'Proofs', 'Obligations',
                            *(str(path).removesuffix('.lean').replace('/', '.')
                              for path in workspace.handwritten(root)
                              if path != Path('Check.lean'))})
    required = ['import Lean', *('import ' + module for module in audit_modules)]
    required += ['open Lean', '']
    if (root / 'verification/aeneas/lean/Arithmetic.lean').exists():
        required += ['attribute [local contract_simps] Zerocopy.Arithmetic.coe_min', '']
    for a in annotations.values():
        if a.get('kind', 'function') != 'function':
            continue
        name = a['theorem']
        required.append(f'example : Zerocopy.Specs.{name} := @Zerocopy.Proofs.{name}')
        required.append(f'check_contract Zerocopy.Obligations.{name} using @Zerocopy.Proofs.{name}')
    required.append('def proofModuleNames : Array Name := #[' + ', '.join('`' + module for module in modules) + ']')
    required.append('def auditModuleNames : Array Name := #[' + ', '.join('`' + module for module in audit_modules) + ']')
    (work / 'Required.lean').write_text('\n'.join(required) + '\n')
    (work / 'Specs.sources.sha256').write_text(manifest['sources'] + '\n')


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
        if implementation['kind'] != 'InherentImplBlock':
            raise ValueError('Only inherent impl roots are supported')
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
        if adt['builtin'] is not None:
            raise ValueError('Builtin Self roots are unsupported')
        self_name = identifiers(type_names.get(adt['id'], []))
        prefix = identifiers(name[:index])
        if not self_name or self_name[:-1] != prefix:
            raise ValueError('Inherent Self must be defined in the annotated module')
        return '::'.join([*self_name, *identifiers(name[index + 1:])])

    roots = {}
    for function in translated['fun_decls']:
        if not function or function['item_meta'].get('started_from') is not True:
            continue
        # A closed type wildcard also selects associated constants. Charon
        # represents their initializers as functions, but they are not methods
        # claiming a separately registered specification. Audit and compile
        # their generated definitions through the ordinary model pipeline.
        if isinstance(function.get('src'), dict) and set(function['src']) == {'GlobalInitializer'}:
            continue
        meta = function['item_meta']
        name = identity(meta['name'])
        if name in roots:
            raise ValueError('Duplicate extracted root identity')
        roots[name] = function
    function_annotations = {rust: a for rust, a in annotations.items()
                            if a.get('kind', 'function') == 'function'}
    if roots.keys() != function_annotations.keys():
        raise ValueError('Extracted roots do not match the annotated inventory')
    for declaration in translated.get('type_decls', []):
        if not declaration:
            continue
        meta = declaration['item_meta']
        # Dependency types may use unsupported external identities. Only local
        # invariant roots participate in this exact source correspondence audit.
        if meta.get('is_local') is not True:
            continue
        rust = identity(meta['name'])
        if rust not in annotations or annotations[rust].get('kind') != 'type':
            continue
        if rust in roots:
            raise ValueError(f'Duplicate extracted type identity: {rust}')
        roots[rust] = declaration
    if roots.keys() != annotations.keys():
        raise ValueError('Extracted type roots do not match the annotated inventory')
    def verify_source(rust, annotation, function):
        meta = function['item_meta']
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
        generics = function['generics']
        if (generics['const_generics'] or generics['trait_clauses']
                or [parameter['name'] for parameter in generics['types']] != annotation['generics']):
            raise ValueError(f'Charon extracted different or unsupported generic parameters for {rust}')

    for rust, annotation in annotations.items():
        function = roots[rust]
        verify_source(rust, annotation, function)
        if annotation.get('kind') == 'type':
            expected = 'Struct' if annotation['nominal_kind'] == 'struct' else 'Enum'
            if not isinstance(function.get('kind'), dict) or set(function['kind']) != {expected}:
                raise ValueError(f'Charon extracted a different or unsupported nominal type for {rust}')
            continue
        body = function.get('body') or {}
        locals_ = body.get('Structured', {}).get('locals', {})
        count = locals_.get('arg_count')
        arguments = locals_.get('locals', [])[1:1 + count] if isinstance(count, int) else []
        if (count != len(annotation['inputs'])
                or len(function['signature']['inputs']) != count
                or [argument['name'] for argument in arguments] != annotation['inputs']):
            raise ValueError(f'Charon extracted different function arguments for {rust}')

    if isinstance(annotations, Annotations):
        extracted_types = {}
        for declaration in translated.get('type_decls', []):
            if not declaration or declaration['item_meta'].get('is_local') is not True:
                continue
            meta = declaration['item_meta']
            kind = declaration.get('kind')
            if not isinstance(kind, dict) or not (set(kind) <= {'Struct', 'Enum'}):
                # Genuine aliases inherit their carrier; unsupported opaque and
                # recursive carriers are diagnosed during structural generation.
                continue
            rust = identity(meta['name'])
            candidates = [a for a in annotations.types if a['rust'] == rust]
            matching = []
            for candidate in candidates:
                try:
                    verify_source(rust, candidate, declaration)
                except ValueError:
                    continue
                matching.append(candidate)
            if len(matching) != 1 or not matching[0]['supported']:
                raise ValueError(f'Extracted nominal type lacks exact supported Rust source ownership: {rust}')
            source = matching[0]
            expected = 'Struct' if source['nominal_kind'] == 'struct' else 'Enum'
            if set(kind) != {expected} or rust in extracted_types:
                raise ValueError(f'Extracted nominal type kind or identity disagrees with Rust source: {rust}')
            extracted_types[rust] = source
        annotations.extracted_types = extracted_types


def update(root, live):
    golden.update(live, root / 'verification/aeneas/golden')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['scan', 'scan-update', 'bindings', 'models', 'render', 'assemble', 'dev-assemble', 'update'])
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--tool', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    args = parser.parse_args()
    policy = inventory(args.root)
    annotations = discover(args.root, args.tool, policy)
    if args.command == 'bindings':
        check_bindings(args.root, annotations, args.work / 'zerocopy.llbc')
    elif args.command == 'models':
        # The driver calls this only after bindings, on freshly generated live
        # output. Keep the verified mapping separate from mutable spec text.
        check_bindings(args.root, annotations, args.work / 'zerocopy.llbc')
        save_bindings(args.root, annotations, args.work)
    elif args.command == 'dev-assemble':
        # Editor-only generation deliberately lacks the fresh extraction/body
        # guarantee. CI uses models above and checks both independent builds.
        save_bindings(args.root, annotations, args.work, development=True)
        assemble(args.root, annotations, args.work, development=True)
    elif args.command == 'update':
        update(args.root, args.work)
    elif args.command == 'assemble':
        assemble(args.root, annotations, args.work)
    elif args.command == 'render':
        render(args.root, args.work)
    else:
        check_goldens(args.root, allow_missing=args.command == 'scan-update')
        write_scan(annotations, policy, args.work)


if __name__ == '__main__':
    main()
