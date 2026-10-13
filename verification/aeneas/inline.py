#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Bind inline contracts to inspected Rust and assemble their Lean projections.

Rust syntax inspection establishes ownership; the independent comment audit
rejects reserved fences that ownership cannot explain. Extraction then binds
those owners to exact source snapshots, parameter order, and generated names.
Assembly consumes that checked binding rather than trusting generated doc names
alone. Development projections use the same authored bytes, with explicit edit
regions whose saved snapshots authorize owner-scoped copy-back.
"""

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
    """Keep authored declarations alongside independently inspected source data.

    The dictionary contains annotations. `types` also retains unannotated nominal
    owners; extraction selects exact supported owners into `extracted_types`.
    `source_snapshots` fixes all inspected Rust, so a later source edit cannot
    inherit an earlier discovery result.
    """

    def __init__(self):
        super().__init__()
        self.types = []
        self.macros = []
        self.extracted_types = None
        self.type_classes = None
        self.external_type_parameters = None
        self.source_snapshots = {}


class GeneratedLines(list):
    """Keep generated lines and their optional Rust locations in one append.

    Maps use one-based Lean line numbers and may omit purely generated lines.
    Recording a location before appending its line prevents framing commands or
    development markers from shifting the mapping away from the intended line.
    The list still preserves the exact ordering and blank lines of assembly.
    """

    def __init__(self, lines):
        super().__init__(lines)
        self.locations = {}

    def append(self, line, location=None):
        if location is not None:
            self.locations[str(len(self) + 1)] = location
        super().append(line)


def suspicious(text):
    """Flag reserved and near-miss fence labels for later ownership checks.

    This is discovery, not admission: only the exact aeneas fence is accepted.
    A lookalike inside a Rust literal is excluded by syntax and lexer inspection.
    """
    return any(word.lower().startswith('aeneas') or
               difflib.SequenceMatcher(None, word.lower(), 'aeneas').ratio() >= 0.7
               for word in MARKER.findall(text))


def read_source(path):
    """Decode source bytes without translating CRLF line endings.

    Physical spelling matters to saved snapshots and reverse-edit spans.
    """
    return path.read_bytes().decode('utf-8')


def rust_identity(file, syntax):
    """Combine the source module path with the syntax owner path.

    lib.rs and mod.rs name their containing module; other filenames add a
    segment. Extraction must later confirm this proposed identity.
    """
    relative = Path(file).relative_to('zerocopy/src')
    modules = list(relative.parent.parts)
    if relative.stem not in ('mod', 'lib'):
        modules.append(relative.stem)
    return '::'.join(['zerocopy', *modules, syntax])


def valid_file(file):
    """Restrict model owners to relative Rust paths under zerocopy/src."""
    return (isinstance(file, str) and file.startswith('zerocopy/src/')
            and '..' not in Path(file).parts and file.endswith('.rs'))


def source_files(root):
    """Inspect all crate Rust sources and reserved-fence candidates elsewhere.

    Unannotated dependencies and inactive cfg alternatives still contribute to
    the exact source snapshot. Disposable build and dependency trees are skipped.
    """
    paths = set()
    for directory, dirs, filenames in os.walk(root):
        dirs[:] = [d for d in dirs if d not in {'.git', 'target', 'vendor', '.lake'}]
        for name in filenames:
            if name.endswith('.rs'):
                path = Path(directory) / name
                relative = str(path.relative_to(root))
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


def code_tokens(text):
    """Mask Lean literal contents after the shared lexer validates them."""
    chars = list(text)
    index = 0
    while index < len(chars):
        char = text[index]
        literal = golden.CHAR.match(text, index) if char == "'" else None
        if literal:
            end = literal.end()
        elif char in ('"', '«'):
            close = '"' if char == '"' else '»'
            end = index + 1
            while end < len(chars):
                if text[end] == '\\' and close == '"':
                    end += 2
                elif text[end] == close:
                    end += 1
                    break
                else:
                    end += 1
        else:
            index += 1
            continue
        for offset in range(index, end):
            if chars[offset] != '\n':
                chars[offset] = ' '
        index = end
    return ''.join(chars)


def checked_payload(text):
    """Validate comments/literals and keep generated command framing private."""
    normalized = '\n'.join(golden.normalize(text))
    if re.search(r'\baeneas_(?:spec|model|invariant)_(?:begin|end)\b', code_tokens(normalized)):
        raise ValueError('Annotation parser framing markers are reserved for generated Lean')
    return normalized


COMMAND = (r'(?:for|proof:|model:|contract|theorem|def|abbrev|axiom|opaque|'
           r'instance|namespace|section|end|import|open|export|attribute|'
           r'set_option|syntax|macro|elab|run_elab|initialize|deriving|'
           r'spec|partial|refines|invariant|model|decode\??|example|constant|inductive|structure|class|mutual|noncomputable|private|protected|public|meta|unsafe|notation|local|scoped|aeneas_\w+|derive_\w+|check_\w+|register_\w+)')


def reject_commands(text):
    """Reject declarations that could escape the authored expression scope.

    Literal contents have been masked, so quoted Lean text does not accidentally
    become a command. The accepted annotation subset remains deliberately small.
    """
    if re.search(r'^\s*(?:' + COMMAND + r'(?=\s|:|$)|#)', code_tokens(text), re.M):
        raise ValueError('Aeneas fence contains an unsupported application or declaration')


def parse_spec(text, generics, inputs):
    """Validate one contract header and its ordered requirements and posts.

    Original Rust parameters are inferred, not authored binders. Ghosts and
    named requirements must not shadow them. Lean checks expression types later.
    """
    normalized = checked_payload(text)
    match = re.match(r'^(?:partial )?spec (' + IDENTIFIER + r')(?=\s|\(|\{|$)', normalized)
    if not match:
        raise ValueError('Aeneas fence requires exactly one spec declaration')
    names, body = binder_header(normalized, match.end())
    if len(set(names)) != len(names):
        raise ValueError('Duplicate specification binder')
    expected = generics + inputs
    if set(names) & set(expected):
        raise ValueError('Ghost binders must not shadow original Rust parameters')
    if any(line and not line.startswith('  ') for line in text.splitlines()[1:]):
        raise ValueError('Specification continuations must be indented by two spaces')
    clauses = normalized[body:]
    reject_commands(clauses)
    if re.search(r'(?m)^\s*(?:requires|ensures)(?!\(raw\)|\s)', clauses):
        raise ValueError('Unsupported clause mode')
    headers = list(re.finditer(r'(?m)^  (requires|ensures)(\(raw\))?\s+', clauses))
    # binder_header skips leading whitespace; restore the first clause's line.
    if re.match(r'(?:requires|ensures)(?:\(raw\))?\s+', clauses):
        clauses = '  ' + clauses
        headers = list(re.finditer(r'(?m)^  (requires|ensures)(\(raw\))?\s+', clauses))
    if not headers or clauses[:headers[0].start()].strip():
        raise ValueError('Specification requires a postcondition; clauses must start on their own lines')
    requirements, seen_post = [], False
    for index, header in enumerate(headers):
        end = headers[index + 1].start() if index + 1 < len(headers) else len(clauses)
        clause = clauses[header.end():end].strip()
        if header[1] == 'requires':
            if seen_post:
                raise ValueError('Requirements must precede postconditions')
            requirement = re.fullmatch(r'(' + IDENTIFIER + r')\s*:\s*(.+)', clause, re.S)
            if not requirement:
                raise ValueError('Requirements must have an explicit name and proposition')
            requirements.append(requirement[1])
        else:
            seen_post = True
            if not re.fullmatch(r'.+?\s*=>\s*.+', clause, re.S):
                raise ValueError('Postconditions require a result pattern and proposition')
    if not seen_post:
        raise ValueError('Specification requires at least one postcondition')
    if len(set(requirements)) != len(requirements) or set(requirements) & set(names + expected):
        raise ValueError('Requirement names must be unique and must not shadow specification binders')
    _, original_body = binder_header(text, re.match(r'^(?:partial )?spec\s+' + IDENTIFIER, text).end())
    clause_line = text[:original_body].count('\n')
    if clause_line == 0 or text[:original_body].rsplit('\n', 1)[1].strip():
        raise ValueError('Specification clauses must begin on their own indented lines')
    return match[1], clause_line


def parse_model(text, generics):
    """Separate one mathematical shape from its local decoder expression.

    Shapes use the original ordered type parameters. Both authored bodies are
    expressions within generated commands, so additional declarations are rejected.
    """
    checked_payload(text)
    shape = re.match(r'^model (' + IDENTIFIER + r')\s*(where|:=)(?=\s|$)', text)
    if not shape or shape[1] in [*generics, 'Fields']:
        raise ValueError('Aeneas type fence requires one model name where fields or model name := type declaration')
    decoders = list(re.finditer(r'^decode(\?)? (' + IDENTIFIER + r')\s*=>[ \t]*', text, re.M))
    if len(decoders) != 1:
        raise ValueError('Aeneas model requires exactly one decode or decode? clause')
    decoder = decoders[0]
    if decoder[2] in generics:
        raise ValueError('Decoder value must not shadow a Rust type parameter')
    shape_text = text[:decoder.start()].rstrip('\n')
    shape_body = text[shape.end():decoder.start()]
    decoder_start = decoder.end() + (text[decoder.end():].startswith('\n'))
    decoder_text = '\n'.join(line[2:] if line.startswith('  ') else line
                             for line in text[decoder_start:].rstrip('\n').splitlines())
    if not shape_body.strip() or not decoder_text.strip():
        raise ValueError('Model shapes and decoders must have nonempty bodies')
    reject_commands(checked_payload(shape_body))
    reject_commands(checked_payload(decoder_text))
    for index, line in enumerate(text.splitlines()):
        if index == 0 or index == text[:decoder.start()].count('\n'):
            continue
        if line and not line.startswith('  '):
            raise ValueError('Model continuations must be indented by two spaces')
    return {'model_name': shape[1], 'shape_text': shape_text,
            'decoder_mode': 'decode?' if decoder[1] else 'decode',
            'value_binder': decoder[2], 'decoder_text': decoder_text,
            'decoder_line': text[:decoder_start].count('\n'),
            'decoder_clause_line': text[:decoder.start()].count('\n'),
            'model_text': text}


def parse_file(source, syntax):
    """Read literal owner docs, then account for every reserved source fence.

    Diagnostic lines describe decoded docs, but copy-back needs physical bytes.
    Only contiguous, uniformly prefixed /// payloads receive writable spans.
    Other accepted literal doc forms remain readable annotations.
    """
    if syntax.get('source') != source:
        raise ValueError('Rust source changed during annotation inspection; retry from a stable source snapshot')

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
                extra = parse_model(payload, owner['generics'])
                name = extra['model_name']
                extra.update(nominal_kind=owner['kind'], fields=owner['fields'])
            close = char_offset(owner['close'])
            declaration = char_offset(owner['start'])
            # Reverse edits use owned physical doc spans, never diagnostic maps.
            physical = source.split('\n')
            physical = [line + '\n' for line in physical[:-1]] + ([physical[-1]] if physical[-1] else [])
            selected = physical[lines[start] - 1:lines[index - 1]]
            prefixes = [re.match(r'^([ \t]*/// ?)', line) for line in selected]
            line_docs = {doc['line'] for doc in docs
                         if source[char_offset(doc['start']):char_offset(doc['end'])].startswith('///')}
            copy_span = None
            if (selected and len(selected) == index - start and all(prefixes)
                    and all(number in line_docs for number in lines[start:index])
                    and len({m[1] for m in prefixes}) == 1
                    and len({'\r\n' if line.endswith('\r\n') else '\n' for line in selected}) == 1):
                begin = len(''.join(physical[:lines[start] - 1]).encode('utf-8'))
                finish = begin + len(''.join(selected).encode('utf-8'))
                copy_span = {'start': begin, 'end': finish, 'prefix': prefixes[0][1],
                             'newline': '\r\n' if selected[0].endswith('\r\n') else '\n'}
            found.append({'syntax': owner['path'], 'kind': kind, 'theorem': name,
                          'copy_span': copy_span,
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


def write_scan(annotations, work):
    """Select exactly the Rust owners of the present annotations as roots.

    CI checks every present specification so an owned fence cannot escape
    extraction, canonical proof checking, or either model's compiled audit.
    """
    (work / 'annotations.json').write_text(json.dumps(annotations, indent=2) + '\n')
    (work / 'source-types.json').write_text(json.dumps(getattr(annotations, 'types', []), indent=2) + '\n')
    (work / 'roots.txt').write_text(','.join(annotations) + '\n')


def discover(root, tool):
    """Capture one inspected snapshot, including unannotated dependency sources.

    Keep every nominal owner, not just annotated types. Generated structural
    models need the same source ownership checks as authored models. Multiple
    cfg alternatives can share a name, so extraction must later select the
    candidate whose source span actually matches.
    """
    paths = source_files(root)
    result = subprocess.run([str(tool)], cwd=root, input=json.dumps(paths), text=True, capture_output=True)
    if result.returncode:
        raise ValueError(f'Rust syntax inspection failed: {result.stderr}')
    syntax = json.loads(result.stdout)
    annotations = Annotations()
    for file in paths:
        source = read_source(root / file)
        try:
            found = parse_file(source, syntax[file])
        except ValueError as error:
            raise ValueError(f'{file}: {error}') from error
        encoded = source.encode('utf-8')
        annotations.source_snapshots[file] = encoded
        if valid_file(file):
            for macro in syntax[file].get('macros', []):
                start = len(encoded[:macro['start']].decode('utf-8'))
                end = len(encoded[:macro['end']].decode('utf-8'))
                annotations.macros.append({
                    'file': file,
                    'modules': macro['modules'],
                    'start': len(source[:start].replace('\r\n', '\n')),
                    'end': len(source[:end].replace('\r\n', '\n')),
                })
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
            if annotation['kind'] == 'function' and annotation['theorem'] in {a['theorem'] for a in annotations.values() if a['kind'] == 'function'}:
                raise ValueError(f'Duplicate specification name: {annotation["theorem"]}')
            annotations[rust] = {**annotation, 'rust': rust, 'file': file}
    if not annotations:
        raise ValueError('No Aeneas specifications discovered')
    return annotations


def check_goldens(root, allow_missing=False):
    """Check the canonical module roster, allowing initial population on request.

    scan-update may start with missing modules, but unexpected files still fail.
    Ordinary scan and later comparison require the complete golden roster.
    """
    directory = root / 'verification/aeneas/golden'
    if allow_missing:
        actual = {str(path.relative_to(directory)) for path in directory.rglob('*') if path.is_file()}
        if actual <= set(golden.FILES):
            return
    golden.files(directory)


def render(root, destination):
    """Copy whole generated goldens while keeping Rust annotations authoritative."""
    generated = golden.files(root / 'verification/aeneas/golden')
    destination.mkdir(parents=True, exist_ok=True)
    for name, text in generated.items():
        (destination / name).write_text(text)


def generated_nominal_types(source):
    """Read local nominal declarations in Aeneas's extracted dependency order.

    These generated names propose the correspondence; inspected source and LLBC
    checks establish its authority. Aliases reuse their existing carrier and
    therefore do not acquire a competing nominal model provider.
    """
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
            # particular they never receive a competing model provider.
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


def generated_type_image(source):
    """Enumerate every raw inductive emitted in Types, including dictionaries.

    The generated spelling proposes a correspondence; verified mode classifies
    its Rust identity independently from LLBC before the compiled Lean audit.
    """
    starts = list(re.finditer(r'^/-- (Trait declaration: )?\[([^\]\n]+)\][^\n]*\n', source, re.M))
    result, seen_rust, seen_raw = [], set(), set()
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else source.rfind('\nend Zerocopy')
        close = source.find('-/\n', match.start(), end)
        if close < 0 or end < 0:
            raise ValueError('Missing generated type documentation or namespace end')
        declaration = source[close + 3:end]
        external_attribute = bool(re.search(r'@\[rust_type\s+"' + re.escape(match[2]) + r'"\]', declaration))
        header = re.search(r'^(structure|inductive) (' + IDENTIFIER + r'(?:\.' + IDENTIFIER + r')*)\b', declaration, re.M)
        if not header:
            if re.search(r'^(?:def|abbrev)\s', declaration, re.M):
                continue
            raise ValueError(f'Unsupported generated type declaration: {match[2]}')
        if match[2] in seen_rust or header[2] in seen_raw:
            raise ValueError(f'Duplicate generated raw type identity: {match[2]}')
        seen_rust.add(match[2])
        seen_raw.add(header[2])
        names, _ = binder_header(declaration, header.end())
        result.append({'rust': match[2], 'raw': 'Zerocopy.' + header[2],
                       'parameters': len(names), 'nominal_kind': 'struct' if header[1] == 'structure' else 'enum',
                       'trait_marker': bool(match[1]), 'external_attribute': external_attribute})
    return result


def generated_bindings(source, annotations, types_source=None):
    """Associate root definitions with pinned Aeneas Rust identity metadata.

    Ignore loop helpers and dependencies, then check original parameter order.
    Names alone do not establish source ownership: the separate LLBC audit also
    binds each annotated root to its inspected body and argument names.
    """
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
                # Called trait implementations have different display names.
                # They remain in the complete model, but cannot own supported
                # annotations. Ignore their labels here; the exact root-set
                # check below still rejects any missing or unsupported root.
                continue
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
            raise ValueError('Generated Types.lean is required to bind type models')
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
    """Hash fixed inspected inputs, rejecting edits since their discovery."""
    snapshots = getattr(annotations, 'source_snapshots', None)
    if not snapshots:
        raise ValueError('Fixed Rust source snapshots are required for model bindings')
    digest = hashlib.sha256()
    for file, snapshot in sorted(snapshots.items()):
        try:
            current = (root / file).read_bytes()
        except OSError as error:
            raise ValueError(f'Scanned source is no longer available: {file}') from error
        if current != snapshot:
            raise ValueError(f'Scanned source changed after annotation discovery: {file}')
        digest.update(file.encode())
        digest.update(snapshot)
    return digest.hexdigest()


def model_digest(work):
    """Fingerprint normalized generated function and nominal-type code.

    Comment-only changes may pass golden comparison, but changed Lean code must
    invalidate the saved binding before projection assembly.
    """
    normalized = '\n'.join(golden.normalize((work / 'Zerocopy/Funs.lean').read_text()))
    types = work / 'Zerocopy/Types.lean'
    if types.exists():
        normalized += '\n' + '\n'.join(golden.normalize(types.read_text()))
    return hashlib.sha256(normalized.encode()).hexdigest()


def save_bindings(root, annotations, work, development=False):
    """Persist a checked name correspondence for both projection builds.

    Live extraction has already selected one source owner per nominal type.
    Development uses the inspected candidates and therefore still requires an
    unambiguous owner. Normalize both paths to candidate lists for the ownership
    check, then use only its selected owners when constructing the manifest.
    """
    source_digest(root, annotations)
    types = work / 'Zerocopy/Types.lean'
    models = generated_bindings((work / 'Zerocopy/Funs.lean').read_text(), annotations,
                                types.read_text() if types.exists() else None)
    nominal = generated_nominal_types(types.read_text()) if types.exists() else []
    extracted_types = getattr(annotations, 'extracted_types', None)
    source_candidates = {}
    if extracted_types is None:
        for source in getattr(annotations, 'types', []):
            source_candidates.setdefault(source['rust'], []).append(source)
    else:
        source_candidates = {rust: [source] for rust, source in extracted_types.items()}
        if {declaration['rust'] for declaration in nominal} != set(extracted_types):
            raise ValueError('Generated nominal type declarations do not match extracted Rust nominal types')
    source_types = {}
    for declaration in nominal:
        candidates = source_candidates.get(declaration['rust'], [])
        if len(candidates) != 1:
            raise ValueError(f'Generated nominal type lacks unambiguous verified source ownership: {declaration["rust"]}')
        source = candidates[0]
        if (not source['supported'] or declaration['generics'] != source['generics']
                or declaration['nominal_kind'] != source['nominal_kind']):
            raise ValueError(f'Generated nominal type disagrees with supported Rust source: {declaration["rust"]}')
        source_types[declaration['rust']] = source
    bindings = {}
    for rust, raw in models.items():
        a = annotations[rust]
        if a.get('kind', 'function') == 'function':
            bindings[rust] = {'kind': 'function', 'raw': 'Zerocopy.' + raw,
                              'generics': a['generics'], 'inputs': a['inputs'],
                              'file': a['file'], 'syntax': a['syntax'], 'spec': a['theorem'],
                              'open_line': a['open_line'], 'end_line': a['end_line'], 'end_col': a['end_col']}
    for declaration in nominal:
        rust = declaration['rust']
        source = source_types[rust]
        a = annotations.get(rust)
        raw = 'Zerocopy.' + declaration['model']
        model_name = a['model_name'] if a and a['kind'] == 'type' else 'Fields'
        bindings[rust] = {'kind': 'type', 'raw': raw, 'fields': raw + '.Fields',
                          'model': raw + '.' + model_name, 'decoder': raw + '.decode',
                          'provider': raw + '.aeneasModel', 'generics': declaration['generics'],
                          'nominal_kind': declaration['nominal_kind'],
                          'authored': bool(a and a['kind'] == 'type'),
                          'macro_expanded': bool(source.get('macro_expanded')),
                          'file': source['file'], 'syntax': source['syntax'],
                          'open_line': source['open_line'], 'end_line': source['end_line'], 'end_col': source['end_col']}
    type_image = []
    classes = getattr(annotations, 'type_classes', None) if not development else None
    if not development and types.exists() and classes is None:
        raise ValueError('Verified live type image requires checked LLBC classification')
    for declaration in generated_type_image(types.read_text()) if types.exists() else []:
        rust = declaration['rust']
        generated_path = rust.removeprefix('zerocopy::').replace('::', '.')
        if declaration['raw'] != 'Zerocopy.' + generated_path:
            raise ValueError(f'Generated raw type name disagrees with extracted Rust identity: {rust}')
        category = classes.get(rust) if classes is not None else (
            'local-nominal' if rust in source_types else
            'trait-dictionary' if declaration['trait_marker'] else
            'external-nominal' if declaration['external_attribute'] else None)
        if category is None:
            raise ValueError(f'Generated raw type lacks classified extraction ownership: {rust}')
        if category == 'local-nominal':
            if (rust not in source_types or declaration['trait_marker'] or declaration['external_attribute']
                    or bindings[rust]['raw'] != declaration['raw']):
                raise ValueError(f'Generated nominal type disagrees with source binding: {rust}')
        elif category == 'trait-dictionary':
            if not declaration['trait_marker'] or declaration['nominal_kind'] != 'struct' or rust in source_types:
                raise ValueError(f'Generated trait dictionary disagrees with extraction: {rust}')
        elif category == 'external-nominal':
            external_parameters = getattr(annotations, 'external_type_parameters', None)
            if (not declaration['external_attribute'] or declaration['trait_marker'] or rust in source_types
                    or (classes is not None and (external_parameters is None
                        or declaration['parameters'] != external_parameters.get(rust)))):
                raise ValueError(f'Generated external nominal type disagrees with extraction: {rust}')
        else:
            raise ValueError(f'Unsupported raw type classification: {category}')
        type_image.append({'rust': rust, 'raw': declaration['raw'],
                           'category': category, 'parameters': declaration['parameters']})
    if {row['rust'] for row in type_image if row['category'] == 'local-nominal'} != set(source_types):
        raise ValueError('Generated raw type image omits a source-bound nominal type')
    manifest = {'version': 3, 'bindings': bindings,
                'type_image': type_image,
                'mode': 'development' if development else 'verified-live',
                'sources': source_digest(root, annotations), 'model': model_digest(work)}
    (work / 'bindings.json').write_text(json.dumps(manifest, indent=2) + '\n')


def assemble(root, annotations, work, development=False):
    """Project checked owners into native Lean modules without replacing code.

    The live binding manifest fixes extracted names and source snapshots. Both
    live and golden builds consume it; development explicitly uses a weaker
    mode. Only authored fragments receive edit markers. Structural derivations,
    function applications, and audit commands remain generated framing.
    """
    if not (root / 'verification/aeneas/lean/RequiredContracts.lean').is_file():
        raise ValueError('RequiredContracts.lean is required for independent specification checks')
    # CI saves this mapping only after exact-body Charon checks and live Aeneas
    # generation. The golden build consumes that same mapping, never its docs.
    saved = work / 'bindings.json'
    if not saved.exists():
        raise ValueError('Verified live model bindings are required before specification generation')
    manifest = json.loads(saved.read_text())
    expected_mode = 'development' if development else 'verified-live'
    if (manifest.get('version') != 3 or manifest.get('mode') != expected_mode
            or manifest.get('sources') != source_digest(root, annotations)
            or manifest.get('model') != model_digest(work)):
        raise ValueError('Model bindings are stale; regenerate specs from the current sources and model')
    if development:
        workspace.protect_projections(work)
    workspace.retire_generated(work)
    bindings = manifest['bindings']
    claimed = {rust for rust, entry in bindings.items() if entry['kind'] == 'function' or entry['authored']}
    if claimed != set(annotations):
        raise ValueError('Verified live bindings do not cover every specification')
    imports = ['module', 'public import Zerocopy.Funs', 'public import SpecPrelude', 'public import SpecsSyntax', 'public import Models']
    if (root / 'verification/aeneas/lean/LayoutModel.lean').exists():
        imports.append('public import LayoutModel')
    elif (root / 'verification/aeneas/lean/Arithmetic.lean').exists():
        imports.append('public import Arithmetic')
    specs = GeneratedLines([*golden.HEADER.rstrip().splitlines(), '', *imports, '@[expose] public section', '',
             'open Aeneas Aeneas.Std', 'open Zerocopy.Proofs', 'namespace Zerocopy.Specs', ''])
    for a in annotations.values():
        if a.get('kind', 'function') != 'function':
            continue
        model = bindings[a['rust']]['raw']
        if not re.fullmatch(IDENTIFIER + r'(?:\.' + IDENTIFIER + ')*', model):
            raise ValueError('Invalid verified generated model name')
        lines = a['spec_text'].rstrip('\n').split('\n')
        clause = a['clause_line']
        application = f'@{model} with {len(a["generics"])} type parameters'
        lines.insert(clause, '  for ' + application)
        specs.append(f'check_model_inputs {model} with {len(a["generics"])} type parameters',
                     {'file': a['file'], 'line': a['source_lines'][0]})
        specs.append('aeneas_spec_begin')
        if development:
            specs.append(f'-- aeneas-copy-begin {a["rust"]} spec')
        for index, line in enumerate(lines):
            original = max(0, index - (index >= clause))
            specs.append(line, {'file': a['file'], 'line': a['source_lines'][original]})
        if development:
            specs.append(f'-- aeneas-copy-end {a["rust"]} spec')
        specs.append('aeneas_spec_end', {'file': a['file'], 'line': a['source_lines'][-1]})
        specs.append(f'check_spec_binding Zerocopy.Specs.{a["theorem"]} '
                     f'for {model} with {len(a["generics"]) + len(a["inputs"])}',
                     {'file': a['file'], 'line': a['source_lines'][0]})
        specs.append('')
    specs.extend(['end Zerocopy.Specs', ''])
    (work / 'Specs.lean').write_text('\n'.join(specs))
    (work / 'Specs.source-map.json').write_text(json.dumps(specs.locations, indent=2) + '\n')
    shape_imports = ['Zerocopy.Types', 'ModelPrelude', 'DeriveModels']
    support = workspace.model_support(root)
    model_imports = ['ModelShapes', 'DeriveModels', *support]
    shapes = GeneratedLines([*golden.HEADER.rstrip().splitlines(), '', 'module',
              *('public import ' + name for name in shape_imports),
              '@[expose] public section', '', 'open Aeneas Aeneas.Std AeneasSpecs', ''])
    decoders = GeneratedLines([*golden.HEADER.rstrip().splitlines(), '', 'module',
                *('public import ' + name for name in model_imports),
                '@[expose] public section', '', 'open Aeneas Aeneas.Std AeneasSpecs', ''])
    # This is the single source/extraction binding table's verified order.
    for rust, entry in bindings.items():
        if entry['kind'] != 'type':
            continue
        raw, count = entry['raw'], len(entry['generics'])
        a = annotations.get(rust)
        if entry['authored']:
            shapes.append(f'aeneas_model_shape {raw} with {count} type parameters begin',
                          {'file': a['file'], 'line': a['source_lines'][0]})
            if development:
                shapes.append(f'-- aeneas-copy-begin {rust} shape')
            for index, line in enumerate(a['shape_text'].splitlines()):
                shapes.append(line, {'file': a['file'], 'line': a['source_lines'][index]})
            if development:
                shapes.append(f'-- aeneas-copy-end {rust} shape')
            location = {'file': a['file'], 'line': a['source_lines'][a['decoder_clause_line']]}
            shapes.append('end', location)
            if development:
                decoders.append(f'derive_rust_model {raw} with {count} type parameters', location)
                decoders.append(f'-- aeneas-copy-begin {rust} decoder')
                decoders.append(f'{a["decoder_mode"]} {a["value_binder"]} =>', location)
            else:
                decoders.append(f'derive_rust_model {raw} with {count} type parameters '
                                f'{a["decoder_mode"]} {a["value_binder"]} =>', location)
            for index, line in enumerate(a['decoder_text'].splitlines()):
                decoders.append('  ' + line, {'file': a['file'],
                    'line': a['source_lines'][min(a['decoder_line'] + index, len(a['source_lines']) - 1)]})
            if development:
                decoders.append(f'-- aeneas-copy-end {rust} decoder')
        else:
            location = {'file': entry['file'], 'line': entry['open_line']}
            shapes.append(f'derive_model_shape {raw} with {count} type parameters', location)
            decoders.append(f'derive_rust_model {raw} with {count} type parameters', location)
        decoders.append(f'check_model_binding {raw} with {count} type parameters', location)
        shapes.append('')
        decoders.append('')
    for module, lines in [('ModelShapes', shapes), ('Models', decoders)]:
        (work / f'{module}.lean').write_text('\n'.join(lines) + '\n')
        (work / f'{module}.source-map.json').write_text(json.dumps(lines.locations, indent=2) + '\n')
    modules = ['Proofs', *sorted(str(path.relative_to(root / 'verification/aeneas/lean')).removesuffix('.lean').replace('/', '.')
                               for path in (root / 'verification/aeneas/lean/Proofs').rglob('*.lean'))]
    # Import every configured native proof module, even when its declarations
    # are unused by the aggregate. Otherwise a private helper could evade the
    # axiom audit simply by being omitted from the aggregate's imports.
    audit_modules = sorted({'Specs', 'ModelShapes', 'Models', 'Zerocopy.Funs', 'Zerocopy.Types',
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
    if source_digest(root, annotations) != manifest['sources']:
        raise ValueError('Source snapshots disagree with verified model bindings')
    (work / 'Specs.sources.sha256').write_text(manifest['sources'] + '\n')
    if development:
        workspace.record_projections(work, annotations)


def check_bindings(root, annotations, llbc):
    """Audit extraction against the complete inspected source snapshot.

    Names alone cannot distinguish cfg alternatives or macro-generated owners.
    Require exact local contents, owner spans, ordered generics, and original
    argument names before accepting the function and nominal-type rosters.
    """
    if isinstance(annotations, Annotations):
        annotations.extracted_types = None
        annotations.type_classes = None
        annotations.external_type_parameters = None
    source_digest(root, annotations)
    translated = json.loads(llbc.read_text())['translated']
    files = {f['id']: f for f in translated['files']}
    if len(files) != len(translated['files']):
        raise ValueError('Duplicate extracted source file identity')
    for file in files.values():
        name = file.get('name')
        if (file.get('contents') is None and isinstance(name, dict)
                and set(name) == {'Local'} and isinstance(name['Local'], str)
                and name['Local'].startswith('/rustc/')):
            # These pinned external sources remain a translation premise.
            continue
        if not isinstance(name, dict) or set(name) != {'Local'}:
            raise ValueError('Unsupported extracted source file identity')
        relative = name['Local']
        path = 'zerocopy/' + relative if isinstance(relative, str) else ''
        if not valid_file(path) or path not in annotations.source_snapshots:
            raise ValueError(f'Extracted local dependency file lacks an inspected source snapshot: {relative}')
        if not isinstance(file.get('contents'), str):
            raise ValueError(f'Extracted local dependency file is missing source contents: {relative}')
        if file['contents'].replace('\r\n', '\n') != annotations.source_snapshots[path].decode('utf-8').replace('\r\n', '\n'):
            raise ValueError(f'Charon extracted a different source body for local dependency file {relative}')
    # At the pinned Charon version named Self types may be deduplicated. Only
    # collect the Adt type domain, not unrelated Value/Deduplicated domains.
    adts = {}

    def collect_adts(value):
        # Charon may store a named Self carrier once and refer to it by index.
        # Gather only the Adt domain: other deduplicated values can reuse the
        # same integer without identifying a type.
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
        # An inherent method name embeds its Self carrier. Resolve that carrier
        # back to the locally defined nominal type instead of accepting a
        # display spelling that could hide a trait or qualified impl.
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
        meta = function['item_meta']
        name = identity(meta['name'])
        if name in roots:
            raise ValueError('Duplicate extracted root identity')
        roots[name] = function
    function_annotations = {rust: a for rust, a in annotations.items()
                            if a.get('kind', 'function') == 'function'}
    if roots.keys() != function_annotations.keys():
        raise ValueError('Extracted roots do not match the present function annotations')
    for declaration in translated.get('type_decls', []):
        if not declaration:
            continue
        meta = declaration['item_meta']
        # Dependency types may use unsupported external identities. Only local
        # model roots participate in this exact source correspondence audit.
        if meta.get('is_local') is not True:
            continue
        rust = identity(meta['name'])
        if rust not in annotations or annotations[rust].get('kind') != 'type':
            continue
        if rust in roots:
            raise ValueError(f'Duplicate extracted type identity: {rust}')
        roots[rust] = declaration
    if roots.keys() != annotations.keys():
        raise ValueError('Extracted type roots do not match the present annotations')
    def verify_source(rust, annotation, function):
        # File equality binds the whole inspected snapshot; the final source
        # position distinguishes same-named cfg alternatives within that file.
        # Normalizing CRLF matches Charon's text convention without discarding
        # physical byte spelling from the editing baseline.
        meta = function['item_meta']
        span = meta['span']['Untagged']
        data = span['data']
        file = files[data['file_id']]
        source = annotations.source_snapshots[annotation['file']].decode('utf-8').replace('\r\n', '\n')
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

    # Charon's deduplicated indices are reused across value domains. Collect
    # definitions only by walking LLBC field-type positions, excluding array
    # lengths and other value domains. Ambiguous type entries fail closed.
    type_tags = {'Scalar', 'TypeVar', 'Adt', 'Array', 'Slice',
                 'Ref', 'RawPtr', 'FnPtr', 'Arrow', 'TraitObject'}
    type_values = {}

    def collect_type_values(value):
        if not isinstance(value, dict) or len(value) != 1:
            return
        tag, body = next(iter(value.items()))
        if tag == 'Value' and isinstance(body, list) and len(body) == 2:
            if (isinstance(body[0], int) and isinstance(body[1], dict)
                    and len(body[1]) == 1 and next(iter(body[1])) in type_tags):
                type_values.setdefault(body[0], []).append(body[1])
            collect_type_values(body[1])
        elif tag in {'Array', 'Slice'} and isinstance(body, list) and body:
            collect_type_values(body[0])
        elif tag == 'Adt' and isinstance(body, dict):
            for parameter in body.get('generics', {}).get('types', []):
                collect_type_values(parameter)

    for declaration in translated.get('type_decls', []):
        if not declaration or not isinstance(declaration.get('kind'), dict):
            continue
        kind = declaration['kind']
        fields = kind.get('Struct', [])
        if 'Enum' in kind:
            fields = [field for variant in kind['Enum'] for field in variant.get('fields', [])]
        if isinstance(fields, list):
            for field in fields:
                if isinstance(field, dict):
                    collect_type_values(field.get('ty'))

    def safe_field_type(ty, parameter_count, seen=frozenset()):
        if not isinstance(ty, dict) or len(ty) != 1:
            return False
        tag, body = next(iter(ty.items()))
        if tag == 'Value':
            return (isinstance(body, list) and len(body) == 2
                    and isinstance(body[0], int) and safe_field_type(body[1], parameter_count, seen))
        if tag == 'Deduplicated':
            if not isinstance(body, int) or body in seen:
                return False
            candidates = {json.dumps(v, sort_keys=True) for v in type_values.get(body, [])}
            return (len(candidates) == 1 and safe_field_type(
                json.loads(next(iter(candidates))), parameter_count, seen | {body}))
        if tag == 'Scalar':
            return isinstance(body, dict)
        if tag == 'TypeVar':
            return (isinstance(body, dict) and set(body) == {'Free'}
                    and isinstance(body['Free'], int) and 0 <= body['Free'] < parameter_count)
        if tag == 'Array':
            return (isinstance(body, list) and len(body) == 3 and body[2] is None
                    and safe_field_type(body[0], parameter_count, seen))
        if tag == 'Slice':
            return (isinstance(body, list) and len(body) == 2 and body[1] is None
                    and safe_field_type(body[0], parameter_count, seen))
        if tag == 'Adt' and isinstance(body, dict):
            generics = body.get('generics', {})
            return (body.get('builtin') is None and isinstance(generics, dict)
                    and generics.get('regions') == [] and generics.get('const_generics') == []
                    and generics.get('trait_refs') == [] and isinstance(generics.get('types'), list)
                    and all(safe_field_type(ty, parameter_count, seen) for ty in generics['types']))
        # In particular, Ref, RawPtr, FnPtr and unrecognized future type forms
        # cannot become structural carriers through a macro source span.
        return False

    def macro_nominal_source(rust, declaration):
        meta = declaration['item_meta']
        span = meta.get('span', {}).get('Untagged', {})
        data = span.get('data', {})
        file = files.get(data.get('file_id'))
        if (meta.get('is_local') is not True or meta.get('started_from') is not False
                or 'source_text' not in meta or meta['source_text'] is not None
                or declaration.get('src') != 'Normal'
                or span.get('generated_from_span') is not None
                or not isinstance(file, dict) or not isinstance(file.get('name'), dict)
                or set(file['name']) != {'Local'}):
            return None
        path = 'zerocopy/' + file['name']['Local']
        if not valid_file(path) or path not in annotations.source_snapshots:
            return None
        source = annotations.source_snapshots[path].decode('utf-8').replace('\r\n', '\n')
        if file.get('contents', '').replace('\r\n', '\n') != source:
            return None

        def position(point):
            if not isinstance(point, dict):
                return None
            line, col = point.get('line'), point.get('col')
            lines = source.split('\n')
            if (not isinstance(line, int) or not isinstance(col, int) or line < 1
                    or line > len(lines) or col < 0 or col > len(lines[line - 1])):
                return None
            return sum(len(part) + 1 for part in lines[:line - 1]) + col

        begin, end = position(data.get('beg')), position(data.get('end'))
        if begin is None or end is None or begin >= end:
            return None
        name = rust.rsplit('::', 1)[-1]
        macros = [macro for macro in annotations.macros if macro['file'] == path
                  and rust_identity(path, '::'.join([*macro['modules'], name])) == rust
                  and macro['start'] <= begin and end <= macro['end']]
        if len(macros) != 1 or suspicious(source[macros[0]['start']:macros[0]['end']]):
            return None
        generics = declaration.get('generics', {})
        if (not isinstance(generics, dict) or generics.get('regions') != []
                or generics.get('const_generics') != [] or generics.get('trait_clauses') != []
                or generics.get('regions_outlive', []) != []
                or generics.get('types_outlive', []) != []
                or generics.get('trait_type_constraints', []) != []
                or not isinstance(generics.get('types'), list)):
            return None
        parameters = [parameter.get('name') for parameter in generics['types']
                      if isinstance(parameter, dict)]
        if (len(parameters) != len(generics['types']) or len(set(parameters)) != len(parameters)
                or any(not isinstance(name, str) or not re.fullmatch(IDENTIFIER, name)
                       for name in parameters)):
            return None
        kind = declaration.get('kind')
        if not isinstance(kind, dict) or len(kind) != 1:
            return None
        nominal_kind, variants = next(iter(kind.items()))
        if nominal_kind == 'Struct' and isinstance(variants, list):
            fields = variants
        elif nominal_kind == 'Enum' and isinstance(variants, list):
            if not all(isinstance(v, dict) and isinstance(v.get('fields'), list) for v in variants):
                return None
            fields = [field for variant in variants for field in variant['fields']]
        else:
            return None
        if not all(isinstance(field, dict) and safe_field_type(field.get('ty'), len(parameters))
                   for field in fields):
            return None
        return {'rust': rust, 'file': path, 'syntax': '::'.join([*macros[0]['modules'], name]),
                'kind': 'type', 'nominal_kind': nominal_kind.lower(), 'generics': parameters,
                'inputs': [], 'supported': True, 'fields': [],
                'open_line': data['beg']['line'], 'end_line': data['end']['line'],
                'end_col': data['end']['col'], 'macro_expanded': True}

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
            if not candidates and rust not in annotations:
                macro_source = macro_nominal_source(rust, declaration)
                if macro_source is not None:
                    matching.append(macro_source)
            if len(matching) != 1 or not matching[0]['supported']:
                raise ValueError(f'Extracted nominal type lacks exact supported Rust source ownership: {rust}')
            source = matching[0]
            expected = 'Struct' if source['nominal_kind'] == 'struct' else 'Enum'
            if set(kind) != {expected} or rust in extracted_types:
                raise ValueError(f'Extracted nominal type kind or identity disagrees with Rust source: {rust}')
            extracted_types[rust] = source
        annotations.extracted_types = extracted_types
        classes = {}
        external_parameters = {}
        for group, category in (('type_decls', None), ('trait_decls', 'trait-dictionary')):
            for declaration in translated.get(group, []):
                if not declaration:
                    continue
                meta = declaration.get('item_meta', {})
                if category is None:
                    kind = declaration.get('kind')
                    if not isinstance(kind, dict) or set(kind) not in ({'Struct'}, {'Enum'}):
                        continue
                    role = ('local-nominal' if meta.get('is_local') is True else
                            'external-nominal' if meta.get('is_local') is False else None)
                else:
                    role = category
                if role is None:
                    continue
                try:
                    rust = identity(meta['name'])
                except (KeyError, TypeError, ValueError):
                    continue
                if rust in classes:
                    raise ValueError(f'Extracted raw type has conflicting declarations: {rust}')
                classes[rust] = role
                if role == 'external-nominal':
                    generics = declaration.get('generics', {})
                    if not isinstance(generics, dict) or not isinstance(generics.get('types'), list):
                        raise ValueError(f'External raw type lacks extracted type parameters: {rust}')
                    external_parameters[rust] = len(generics['types'])
        annotations.type_classes = classes
        annotations.external_type_parameters = external_parameters


def update(root, live):
    """Update complete goldens from live output without rewriting Rust fences."""
    golden.update(live, root / 'verification/aeneas/golden')


def main():
    """Route discovery, extraction checks, and assembly through their boundaries.

    Development assembly is explicitly weaker than fresh live binding; both
    modes still preserve projection edits and bind to inspected snapshots.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['scan', 'scan-update', 'bindings', 'models', 'render', 'assemble', 'dev-assemble', 'update'])
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--tool', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    args = parser.parse_args()
    annotations = discover(args.root, args.tool)
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
        workspace.protect_projections(args.work)
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
        write_scan(annotations, args.work)


if __name__ == '__main__':
    main()
