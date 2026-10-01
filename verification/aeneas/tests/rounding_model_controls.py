# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Mutate only the production rounding decoder and recognize its semantic failure."""
import argparse
import json
from pathlib import Path
import re

OWNER = 'Zerocopy.layout.RoundingAlignAndPhase'
PREFIX = f'derive_rust_model {OWNER} with 0 type parameters'
CONSTANT = PREFIX + """ decode self =>
  { align := 1, phase := 0, align_pow2 := AeneasSpecs.model_power_of_two 0,
    phase_lt := by decide,
    fits := by
      have positive := self._0.positive
      have bound : self._0.value ≤ Usize.max := by
        simpa only [UScalar.max, Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq]
          using self._0.bound
      omega }
"""
REJECT = PREFIX + ' decode? self =>\n  none\n'


def capability():
    manifest = json.loads(Path('bindings.json').read_text())
    entries = manifest.get('bindings')
    if manifest.get('version') != 3 or manifest.get('mode') != 'verified-live' or not isinstance(entries, dict):
        raise ValueError('Invalid verified binding table for rounding model controls')
    owner = entries.get('zerocopy::layout::RoundingAlignAndPhase')
    if owner is not None and not isinstance(owner, dict):
        raise ValueError('Invalid production rounding owner binding')
    selected = bool(owner and owner.get('kind') == 'type' and owner.get('raw') == OWNER
                    and owner.get('model') == OWNER + '.RoundingValue')
    if Path('RepresentationLaws.lean').exists() and not selected:
        raise ValueError('Rounding representation laws lost their production model binding')
    if selected:
        for name in ('Models', 'ModelShapes', 'MathViews', 'RepresentationLaws'):
            if not Path(name + '.lean').is_file():
                raise ValueError(f'Missing selected rounding model control prerequisite: {name}')
    return selected


def mutate(kind):
    if kind not in ('constant', 'none'):
        raise ValueError('Unknown rounding decoder mutation')
    path = Path('Models.lean')
    text = path.read_text()
    end_marker = f'check_model_binding {OWNER} with 0 type parameters'
    if text.count(PREFIX) != 1 or text.count(end_marker) != 1:
        raise ValueError('Rounding decoder control boundaries no longer match')
    start = text.index(PREFIX)
    end = text.index(end_marker)
    if end <= start or re.search(r'^(?:derive_rust_model|check_model_binding|namespace|end|'
                                 r'def|abbrev|instance|theorem|structure|inductive)\b',
                                 text[start + len(PREFIX):end], re.MULTILINE):
        raise ValueError('Rounding decoder control boundaries contain another declaration')
    # Keep every generated sibling, raw owner, and child provider untouched.
    path.write_text(text[:start] + (CONSTANT if kind == 'constant' else REJECT) + text[end:])


def check_failure(kind, log_path):
    if kind not in ('constant', 'none'):
        raise ValueError('Unknown rounding decoder mutation')
    module, theorem = (('MathViews', 'encoding_valid_iff') if kind == 'none'
                       else ('RepresentationLaws', 'rounding_decode_components'))
    lines = Path(module + '.lean').read_text().splitlines()
    starts = [i + 1 for i, line in enumerate(lines) if re.search(r'\btheorem\s+' + theorem + r'\b', line)]
    if len(starts) != 1:
        raise ValueError(f'Missing independent rounding law: {module}.{theorem}')
    start = starts[0]
    end = next((i + 1 for i, line in enumerate(lines) if i + 1 > start
                and re.match(r'^(?:@\[[^]]*\]\s*)?(?:theorem|def|abbrev)\s', line)), len(lines) + 1)
    text = re.sub(r'\x1b\[[0-9;]*m', '', Path(log_path).read_text())
    # A parser, import, missing dependency, or unknown kernel constant is never
    # evidence that the independent mathematical proposition rejects a decoder.
    invalid = (r'unknown (?:identifier|constant|module)', r'(?:invalid|failed to) import',
               r'object file .*does not exist', r'unexpected token',
               r'environment already contains', r'failed to synthesize',
               r'kernel (?:exception|error)', r'could not resolve import')
    if any(re.search(marker, text, re.IGNORECASE) for marker in invalid):
        raise ValueError('Rounding mutant failed outside its independent semantic law')
    # Lean's native renderer puts the severity after the location; Lake puts it
    # before the location. Parse every error, including unlocated errors, so a
    # semantic failure cannot hide a broken import or kernel failure.
    severity = r'error(?:\([^)]*\))?'
    native = re.compile(r'^(.+[.]lean):(\d+):\d+: ' + severity + r': (.*)$')
    lake = re.compile(r'^' + severity + r': (.+[.]lean):(\d+):\d+: (.*)$')
    summaries = ('error: Lean exited with code 1', 'error: build failed')
    errors = []
    for line in text.splitlines():
        match = native.match(line) or lake.match(line)
        if match:
            file, location, diagnostic = match.groups()
            errors.append((Path(file).name, int(location), diagnostic))
        elif re.search(r'\berror(?:\([^)]*\))?:', line) and line not in summaries:
            raise ValueError('Unrecognized error in rounding semantic rejection log')
    expected = ('unsolved goals', 'Application type mismatch', 'Type mismatch', 'Tactic')
    if not errors or any(not diagnostic.startswith(expected) for _, _, diagnostic in errors):
        raise ValueError('Rounding mutant failed outside its independent semantic law')
    if not any(file == module + '.lean' and start <= line < end
               and any(diagnostic.startswith(prefix) for prefix in expected)
               for file, line, diagnostic in errors):
        raise ValueError(f'No semantic rejection at {module}.{theorem}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=('capability', 'mutate', 'check-failure'))
    parser.add_argument('kind', nargs='?', choices=('constant', 'none'))
    parser.add_argument('log', nargs='?')
    args = parser.parse_args()
    if args.operation == 'capability':
        print('yes' if capability() else 'no')
    elif args.operation == 'mutate':
        if args.kind is None:
            parser.error('mutate requires a decoder mutation')
        mutate(args.kind)
    else:
        if args.kind is None or args.log is None:
            parser.error('check-failure requires a mutation and log')
        check_failure(args.kind, args.log)


if __name__ == '__main__':
    main()
