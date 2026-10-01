#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Copy one marked development projection into its original owned /// fence.

The persisted generation snapshot is reverse-edit authority. Source maps only
explain Lean diagnostics. Rust and the baseline have separate atomic writes;
an interrupted baseline write is reconciled against the exact planned Rust.
"""

import copy
import difflib
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import tempfile

MODULES = ('ModelShapes', 'Models', 'Specs')
STATE = '.inline-projections.json'
OWNER = r'zerocopy(?:::[A-Za-z_][A-Za-z_0-9]*)+'
MARK = re.compile(r'^-- aeneas-copy-(begin|end) (' + OWNER + r') (spec|shape|decoder)\n', re.M)
PART_MODULE = {'spec': 'Specs', 'shape': 'ModelShapes', 'decoder': 'Models'}


def digest(text):
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def regions(text):
    """Return strict marker framing, rejecting nested, fake and duplicate marks."""
    pieces, values, position, active = [], {}, 0, None
    matches = list(MARK.finditer(text))
    # Even a malformed or embedded lookalike must not become authored content.
    if text.count('aeneas-copy-') != len(matches):
        raise ValueError('Malformed copy-back marker')
    for match in matches:
        key = (match[2], match[3])
        if match[1] == 'begin':
            if active is not None or key in values:
                raise ValueError('Nested or duplicate copy-back marker')
            pieces.append(text[position:match.end()])
            active = (key, match.end())
        else:
            if active is None or active[0] != key:
                raise ValueError('Unmatched copy-back marker')
            values[key] = text[active[1]:match.start()]
            pieces.append(key)
            position, active = match.start(), None
    if active is not None:
        raise ValueError('Unterminated copy-back marker')
    pieces.append(text[position:])
    return pieces, values


def render(pieces, values):
    return ''.join(values[piece] if isinstance(piece, tuple) else piece for piece in pieces)


def authored(entry, values):
    import inline
    owner = entry['rust']
    if entry['kind'] == 'function':
        text = values[(owner, 'spec')]
        lines = text.splitlines(keepends=True)
        application = entry['for_line'] + '\n'
        if lines.count(application) != 1:
            raise ValueError('Generated for target must remain exactly unchanged')
        application_index = lines.index(application)
        lines.remove(application)
        payload = ''.join(lines)
        _, clause_line = inline.parse_spec(payload, entry['generics'], entry['inputs'])
        if application_index != clause_line:
            raise ValueError('Generated for target must remain immediately before the first specification clause')
        # Match assemble's projection rules before acknowledging edited text.
        # A later regeneration must reproduce every selected authored byte.
        projected = payload.rstrip('\n').split('\n')
        projected.insert(clause_line, entry['for_line'])
        if text != '\n'.join(projected) + '\n':
            raise ValueError('Specification formatting would change on regeneration; '
                             'remove trailing blank lines from the authored region and retry')
    else:
        payload = values[(owner, 'shape')].rstrip('\n') + '\n' + values[(owner, 'decoder')]
        model = inline.parse_model(payload, entry['generics'])
        shape = '\n'.join(model['shape_text'].splitlines()) + '\n'
        decoder = (f'{model["decoder_mode"]} {model["value_binder"]} =>\n' +
                   ''.join('  ' + line + '\n' for line in model['decoder_text'].splitlines()))
        if values[(owner, 'shape')] != shape or values[(owner, 'decoder')] != decoder:
            raise ValueError('Model formatting would change on regeneration; remove trailing blank lines, '
                             'put the decode/decode? body on separate lines indented by two spaces, and retry')
    if not payload.endswith('\n') or '\r' in payload or '```' in payload:
        raise ValueError('Authored payload requires LF lines without Rust fence delimiters')
    return payload


def record(work, annotations):
    projections = {name: (work / f'{name}.lean').read_bytes().decode('utf-8') for name in MODULES}
    all_values = {}
    for text in projections.values():
        all_values.update(regions(text)[1])
    owners, sources = {}, {}
    for rust, annotation in annotations.items():
        entry = {key: annotation[key] for key in ('rust', 'file', 'kind', 'generics', 'inputs', 'copy_span')}
        entry['payload'] = annotation['spec_text'] if entry['kind'] == 'function' else annotation['model_text']
        if entry['kind'] == 'function':
            candidates = [line for line in all_values[(rust, 'spec')].splitlines() if line.startswith('  for ')]
            if len(candidates) != 1:
                raise ValueError('Missing generated specification application')
            entry['for_line'] = candidates[0]
        owners[rust] = entry
        sources[entry['file']] = annotations.source_snapshots[entry['file']].decode('utf-8')
    state = {'version': 2, 'sha256': {name: digest(text) for name, text in projections.items()},
             'projections': projections, 'owners': owners, 'sources': sources}
    validate(state)
    (work / STATE).write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n')


def validate(state):
    """Validate a baseline completely before using any saved edit authority."""
    import inline
    try:
        if (not isinstance(state, dict) or set(state) != {'version', 'sha256', 'projections', 'owners', 'sources'}
                or state['version'] != 2 or set(state['sha256']) != set(MODULES)
                or set(state['projections']) != set(MODULES) or not state['owners']):
            raise ValueError('Copy-back requires a complete version 2 baseline; regenerate clean projections to upgrade')
        values = {}
        for module in MODULES:
            text = state['projections'][module]
            if not isinstance(text, str) or state['sha256'][module] != digest(text):
                raise ValueError('Projection baseline digest disagrees with saved text')
            parts = regions(text)[1]
            if any(PART_MODULE[part] != module for _, part in parts):
                raise ValueError('Projection region is in the wrong module')
            values.update(parts)
        expected, spans = set(), {}
        if set(state['sources']) != {e['file'] for e in state['owners'].values()}:
            raise ValueError('Source snapshot roster disagrees with owners')
        for owner, entry in state['owners'].items():
            keys = {'rust', 'file', 'kind', 'generics', 'inputs', 'copy_span', 'payload'}
            if entry.get('kind') == 'function':
                keys.add('for_line')
            if (set(entry) != keys or entry['rust'] != owner or not re.fullmatch(OWNER, owner)
                    or entry['kind'] not in ('function', 'type') or not inline.valid_file(entry['file'])
                    or any(not isinstance(entry[k], list) or any(not isinstance(n, str) or
                           not re.fullmatch(inline.IDENTIFIER, n) for n in entry[k]) for k in ('generics', 'inputs'))):
                raise ValueError('Invalid saved annotation ownership')
            expected.update((owner, part) for part in (['spec'] if entry['kind'] == 'function' else ['shape', 'decoder']))
            # Decode the original authored projection independently of Rust's doc
            # spelling. Inline decoders are canonically expanded onto two lines.
            original = authored(entry, values)
            if entry['kind'] == 'function':
                # Forward assembly strips final empty specification lines; the
                # complete source payload remains authoritative for no-op edits.
                equivalent = original == entry['payload'].rstrip('\n') + '\n'
            else:
                before = inline.parse_model(entry['payload'], entry['generics'])
                after = inline.parse_model(original, entry['generics'])
                equivalent = all(before[k] == after[k] for k in ('shape_text', 'decoder_mode', 'value_binder', 'decoder_text'))
            if not equivalent:
                raise ValueError('Saved projection disagrees with original annotation')
            span = entry['copy_span']
            if span is None:
                continue  # Existing block/attribute docs remain readable, not writable.
            if (not isinstance(span, dict) or set(span) != {'start', 'end', 'prefix', 'newline'}
                    or type(span['start']) is not int or type(span['end']) is not int
                    or not 0 <= span['start'] < span['end']
                    or not re.fullmatch(r'[ \t]*/// ?', span['prefix']) or span['newline'] not in ('\n', '\r\n')):
                raise ValueError('Invalid owned doc payload span')
            source = state['sources'][entry['file']].encode('utf-8')
            if span['end'] > len(source):
                raise ValueError('Owned doc span escapes source snapshot')
            text = source[span['start']:span['end']].decode('utf-8')
            lines = text.splitlines(keepends=True)
            if (not lines or any(not line.startswith(span['prefix']) or not line.endswith(span['newline']) for line in lines)
                    or ''.join(line[len(span['prefix']):-len(span['newline'])] + '\n' for line in lines) != entry['payload']
                    or (span['start'] and source[span['start'] - 1:span['start']] != b'\n')
                    or not re.fullmatch(rb'[ \t]*/// ```aeneas\r?\n', source[:span['start']].splitlines(keepends=True)[-1])
                    or not re.match(rb'[ \t]*/// ```\r?\n', source[span['end']:])):
                raise ValueError('Owned doc payload disagrees with original source fence')
            spans.setdefault(entry['file'], []).append((span['start'], span['end']))
        if set(values) != expected:
            raise ValueError('Copy-back marker roster disagrees with saved ownership')
        for file_spans in spans.values():
            ordered = sorted(file_spans)
            if any(a[1] > b[0] for a, b in zip(ordered, ordered[1:])):
                raise ValueError('Owned annotation payload spans overlap')
    except (KeyError, TypeError, AttributeError, UnicodeError, IndexError) as error:
        raise ValueError('Malformed projection baseline') from error


def checked_file(root, relative):
    """Reject escaping and symlinks; remember parent and file identities."""
    path = Path(relative)
    if path.is_absolute() or not path.parts or any(p in ('.', '..') for p in path.parts):
        raise ValueError('Copy-back path must stay inside the repository')
    parents = []
    current = root
    for part in (None, *path.parts):
        if part is not None:
            current = current / part
        info = current.lstat()
        if stat.S_ISLNK(info.st_mode):
            raise ValueError(f'Copy-back refuses symlink traversal: {current}')
        parents.append((current, info.st_dev, info.st_ino, info.st_mode))
    if not stat.S_ISREG(info.st_mode):
        raise ValueError(f'Copy-back requires a regular file: {current}')
    return {'path': current, 'identities': parents, 'bytes': current.read_bytes(), 'mode': stat.S_IMODE(info.st_mode)}


def unchanged(record):
    for path, device, inode, mode in record['identities']:
        info = path.lstat()
        if (info.st_dev, info.st_ino, info.st_mode) != (device, inode, mode):
            raise ValueError(f'Copy-back input identity changed: {path}')
    if record['path'].read_bytes() != record['bytes']:
        raise ValueError(f'Copy-back input changed: {record["path"]}')


def replace(record, contents, guard):
    """Atomic file replacement, with an immediately preceding input guard."""
    path = record['path']
    descriptor, temporary = tempfile.mkstemp(prefix='.aeneas-copy-', dir=path.parent)
    try:
        with os.fdopen(descriptor, 'wb') as stream:
            os.fchmod(stream.fileno(), record['mode'])
            stream.write(contents)
            stream.flush()
            os.fsync(stream.fileno())
        guard()
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def copy_back(root, work, owner, apply=False, after_source_write=None):
    """Plan without writes; apply accepts only the exact before or after Rust."""
    root, work = Path(root).absolute(), Path(work).absolute()
    try:
        relative_work = work.relative_to(root)
    except ValueError as error:
        raise ValueError('Copy-back project must be inside the repository') from error
    if not re.fullmatch(OWNER, owner):
        raise ValueError('Copy-back requires the full Rust owner identity')
    control = checked_file(root, relative_work / STATE)
    try:
        state = json.loads(control['bytes'])
    except (ValueError, UnicodeError) as error:
        raise ValueError('Malformed projection baseline') from error
    validate(state)
    if owner not in state['owners']:
        raise ValueError('Rust owner is absent from the generation baseline')
    entry = state['owners'][owner]
    if entry['copy_span'] is None:
        raise ValueError('Copy-back supports only contiguous uniformly indented /// fences; other doc forms are read-only')
    records, current_values, layouts = [control], {}, {}
    for module in MODULES:
        record_ = checked_file(root, relative_work / f'{module}.lean')
        records.append(record_)
        current = record_['bytes'].decode('utf-8')
        layout, values = regions(current)
        original_layout, original_values = regions(state['projections'][module])
        if layout != original_layout or values.keys() != original_values.keys():
            raise ValueError(f'Edits outside authored regions in {module}.lean are unsupported')
        layouts[module] = original_layout
        current_values.update(values)
    payload = authored(entry, current_values)
    source = checked_file(root, entry['file'])
    records.append(source)
    before = state['sources'][entry['file']].encode('utf-8')
    span = entry['copy_span']
    # Keep a physically unchanged fence unchanged, including inline decode
    # spelling, when the selected authored regions have no edits.
    baseline_values = {}
    for text in state['projections'].values():
        baseline_values.update(regions(text)[1])
    selected = {key for key in baseline_values if key[0] == owner}
    edited = any(current_values[key] != baseline_values[key] for key in selected)
    if not edited:
        payload = entry['payload']
    replacement = ''.join(span['prefix'] + line + span['newline'] for line in payload[:-1].split('\n')).encode('utf-8')
    after = before[:span['start']] + replacement + before[span['end']:]
    if source['bytes'] not in (before, after):
        raise ValueError('Rust source changed since generation; copy-back has no writes')
    diff = ''.join(difflib.unified_diff(before.decode('utf-8').splitlines(keepends=True),
                                      after.decode('utf-8').splitlines(keepends=True),
                                      fromfile=entry['file'], tofile=entry['file']))
    print(diff, end='')
    if not diff:
        print(f'No Rust payload changes for {owner}.')
    if not apply:
        return diff
    updated = copy.deepcopy(state)
    for module, layout in layouts.items():
        values = regions(state['projections'][module])[1]
        values.update({key: current_values[key] for key in selected if key in values})
        updated['projections'][module] = render(layout, values)
        updated['sha256'][module] = digest(updated['projections'][module])
    delta = len(replacement) - (span['end'] - span['start'])
    updated['sources'][entry['file']] = after.decode('utf-8')
    updated['owners'][owner]['payload'] = payload
    for other, annotation in updated['owners'].items():
        other_span = annotation['copy_span']
        if annotation['file'] != entry['file'] or other_span is None:
            continue
        if other == owner:
            other_span['end'] += delta
        elif other_span['start'] >= span['end']:
            other_span['start'] += delta
            other_span['end'] += delta
    validate(updated)

    def guard():
        for record_ in records:
            unchanged(record_)

    guard()
    if source['bytes'] != after:
        replace(source, after, guard)
        records[-1] = checked_file(root, entry['file'])
        if records[-1]['bytes'] != after:
            raise ValueError('Rust source changed after replacement; retain projections and baseline for recovery')
        if after_source_write is not None:
            after_source_write()
    encoded = (json.dumps(updated, ensure_ascii=False, indent=2) + '\n').encode('utf-8')
    if encoded != control['bytes']:
        replace(control, encoded, guard)
    return diff
