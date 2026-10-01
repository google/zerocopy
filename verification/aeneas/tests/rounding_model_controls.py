# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Challenge rounding operation promises and input coverage with valid decoders.

The constant decoder still constructs a constrained mathematical value but loses
the constructor's promised pair. The rejecting decoder excludes an independently
fixed valid getter input. Both probes first pass with the production decoder;
negative-controls.sh also compiles each mutated decoder before checking failure.
Only a diagnostic inside the intended theorem counts as semantic rejection.
"""
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
PROBES = {'constant': ('RoundingConstructorControl', 'constructor_promise'),
          'none': ('RoundingDomainControl', 'positive_input_domain')}


def constructor_spec():
    """Reuse the source-owned fence verbatim, without its helper import closure."""
    source = Path('Specs.lean').read_text()
    fences = re.findall(r'^aeneas_spec_begin\n(.*?)^aeneas_spec_end$',
                        source, re.MULTILINE | re.DOTALL)
    matches = [body for body in fences if re.match(r'spec encoding_new_spec\b', body)]
    if len(matches) != 1 or not re.search(
            r'for @?' + re.escape(OWNER) + r'[.]new with 0 type parameters\b', matches[0]):
        raise ValueError('Missing unique source-owned rounding constructor promise')
    return matches[0]


def write_probes():
    """Write isolated Lean consumers of the real constructor fence and decoder.

    The fixed raw input and successful raw result prevent changed admission from
    making the promises vacuous. Imports supply ordinary decoder dependencies;
    representation helper lemmas cannot replace the operation being challenged.
    """
    header = '''module
public import Zerocopy.Funs
public import Models
public import SpecsSyntax
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
set_option linter.unusedSimpArgs false
'''
    constructor = header + '''namespace RoundingConstructorControl
-- This is the unchanged generated constructor fence, in an isolated namespace.
''' + constructor_spec() + '''
def align : core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner := ⟨2#usize⟩
def phase : Usize := 1#usize
def code : Zerocopy.layout.RoundingAlignAndPhase := ⟨⟨3#usize⟩⟩
-- Pin the actual successful result independently of the decoder.
theorem constructor_result : Zerocopy.layout.RoundingAlignAndPhase.new align phase = .ok code := by
  have pow : (2 : Nat).isPowerOfTwo := by simpa using model_power_of_two 1
  rcases System.Platform.numBits_eq with bits | bits <;>
    simp [Zerocopy.layout.RoundingAlignAndPhase.new, align, phase, code,
      core.num.nonzero.NonZero.get, core.num.nonzero.NonZero.new,
      core.num.Usize.is_power_of_two, UScalar.is_power_of_two,
      UScalar.lt_equiv, UScalar.eq_equiv, UScalar.val_or, massert, lift, pow, bits]
-- The arbitrary-outcome contract checks both output admission and pair meaning.
theorem constructor_promise : encoding_new_spec_contract align phase (.ok code) := by
  simp [encoding_new_spec_contract, WP.spec, WP.dspec, RustModel.decode,
    Zerocopy.layout.RoundingAlignAndPhase.aeneasModel,
    Zerocopy.layout.RoundingAlignAndPhase.decode,
    Zerocopy.layout.RoundingAlignAndPhase.decodeFields,
    modelNonZeroUScalar, modelUScalar, unsignedWord, align, phase, code]
end RoundingConstructorControl
'''
    domain = header + '''namespace RoundingDomainControl
def code : Zerocopy.layout.RoundingAlignAndPhase := ⟨⟨3#usize⟩⟩
-- Independently fix a positive input required by the getter domain. A shared
-- rejecting decoder cannot turn this promised raw input into a vacuous premise.
theorem positive_input_domain : isValid code := by
  simp [isValid, RustModel.decode,
    Zerocopy.layout.RoundingAlignAndPhase.aeneasModel,
    Zerocopy.layout.RoundingAlignAndPhase.decode,
    Zerocopy.layout.RoundingAlignAndPhase.decodeFields,
    modelNonZeroUScalar, modelUScalar, unsignedWord, code]
end RoundingDomainControl
'''
    for module, source in [('RoundingConstructorControl', constructor),
                           ('RoundingDomainControl', domain)]:
        path = Path(module + '.lean')
        if path.exists():
            raise ValueError(f'Rounding operation control fixture already exists: {module}')
    Path('RoundingConstructorControl.lean').write_text(constructor)
    Path('RoundingDomainControl.lean').write_text(domain)


def capability():
    """Select controls from the audited owner binding, not from helper names.

    Earlier stack stages may lack this model. Once its owner or decoder is
    present, missing or changed binding evidence is an error, never a skip.
    """
    manifest = json.loads(Path('bindings.json').read_text())
    entries = manifest.get('bindings')
    if manifest.get('version') != 3 or manifest.get('mode') != 'verified-live' or not isinstance(entries, dict):
        raise ValueError('Invalid verified binding table for rounding model controls')
    owner = entries.get('zerocopy::layout::RoundingAlignAndPhase')
    if owner is not None and not isinstance(owner, dict):
        raise ValueError('Invalid production rounding owner binding')
    selected = bool(owner and owner.get('kind') == 'type' and owner.get('raw') == OWNER
                    and owner.get('model') == OWNER + '.RoundingValue')
    if not selected and (owner is not None or (Path('Models.lean').exists()
                                              and PREFIX in Path('Models.lean').read_text())):
        raise ValueError('Rounding operation controls lost their production model binding')
    if selected:
        for name in ('Models', 'ModelShapes', 'Specs', 'SpecsSyntax', 'Zerocopy/Funs'):
            if not Path(name + '.lean').is_file():
                raise ValueError(f'Missing selected rounding model control prerequisite: {name}')
    return selected


def mutate(kind):
    """Replace only the unique owner's decoder, preserving sibling providers."""
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
    """Accept only recognized proof failures within the selected probe theorem.

    Inspect all errors, not merely the first expected one. An unrelated import,
    parser, or kernel failure invalidates the evidence even when the semantic
    probe also fails. Accept both native Lean and Lake diagnostic locations.
    """
    if kind not in ('constant', 'none'):
        raise ValueError('Unknown rounding decoder mutation')
    module, theorem = PROBES[kind]
    lines = Path(module + '.lean').read_text().splitlines()
    starts = [i + 1 for i, line in enumerate(lines) if re.search(r'\btheorem\s+' + theorem + r'\b', line)]
    if len(starts) != 1:
        raise ValueError(f'Missing rounding behavior probe: {module}.{theorem}')
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
        raise ValueError('Rounding mutant failed outside its operation promise or domain')
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
    if not errors or any(file != module + '.lean' or not start <= line < end
                         or not diagnostic.startswith(expected)
                         for file, line, diagnostic in errors):
        raise ValueError('Rounding mutant failed outside its operation promise or domain')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=('capability', 'write-probes', 'mutate', 'check-failure'))
    parser.add_argument('kind', nargs='?', choices=('constant', 'none'))
    parser.add_argument('log', nargs='?')
    args = parser.parse_args()
    if args.operation == 'capability':
        print('yes' if capability() else 'no')
    elif args.operation == 'write-probes':
        write_probes()
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
