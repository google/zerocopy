# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Challenge original/final const identity using a real native extraction.

The files are read-only. Each mutation changes an in-memory compiler record,
then restores it before the next control. A successful baseline is mandatory;
a broken extraction or missing native manifest never counts as rejection.
"""

import copy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import inline
import trait_invariants as traits


def check(work):
    final = json.loads((work / 'zerocopy.llbc').read_text())['translated']
    before = json.loads((work / 'zerocopy.before.ullbc').read_text())['translated']
    annotations = inline.Annotations()
    annotations.update(json.loads((work / 'annotations.json').read_text()))
    annotations.trait_proofs = json.loads((work / 'trait-proofs.json').read_text())
    evidence = json.loads((work / 'annotation-origins.json').read_text())
    root = Path(__file__).resolve().parents[3]
    annotations.source_snapshots = {
        'zerocopy/' + source['file']: (root / 'zerocopy' / source['file']).read_bytes()
        for source in evidence['sources']}
    inline.reconcile_origins(annotations, evidence, before)

    def bind():
        return traits.bind_laws(annotations, work, final, before)

    laws, implementations, _ = bind()
    into_bytes = [law for law in laws if law['rust'] == 'zerocopy::IntoBytes']
    if len(into_bytes) != 1:
        raise AssertionError('Control requires the actual annotated IntoBytes trait')
    arrays = [row for row in implementations
              if row['trait_def_id'] == into_bytes[0]['def_id']
              and row['const_count'] == 1
              and row['rust_type'] == [['array', ['parameter', 0], ['const_parameter', 0]]]]
    if len(arrays) != 1:
        raise AssertionError('Control requires exactly one original generic array impl')
    ident = arrays[0]['def_id']
    extracted = traits.declarations(final, 'trait_impls')[ident]
    original = traits.declarations(before, 'trait_impls')[ident]

    def length(implementation):
        array = traits.unwrap(implementation['impl_trait']['generics']['types'][0])['Array']
        return traits.unwrap(array[1])

    controls = [
        ('final omitted const', extracted,
         lambda impl: impl['generics'].update(const_generics=[])),
        ('original omitted const', original,
         lambda impl: impl['generics'].update(const_generics=[])),
        ('final wrong const name', extracted,
         lambda impl: impl['generics']['const_generics'][0].update(name='Other')),
        ('original wrong const application', original,
         lambda impl: length(impl)[0].update(Var={'Bound': [0, 1]})),
        ('final wrong const application', extracted,
         lambda impl: length(impl)[0].update(Var={'Free': 1})),
        ('final fixed length replacement', extracted,
         lambda impl: length(impl).__setitem__(0, {'Integer': {'Unsigned': ['Usize', '3']}})),
    ]
    checked = []
    for label, implementation, mutate in controls:
        saved = copy.deepcopy(implementation)
        try:
            mutate(implementation)
            try:
                bind()
            except ValueError as error:
                diagnostic = str(error)
                if not any(reason in diagnostic for reason in (
                        'original const parameters', 'omitted original parameter',
                        'original Rust type application')):
                    raise AssertionError(f'{label}: unintended rejection: {diagnostic}') from error
                checked.append({'control': label, 'diagnostic': diagnostic})
            else:
                raise AssertionError(f'{label}: missing const admission rejection')
        finally:
            implementation.clear()
            implementation.update(saved)
    # Confirm each mutation restored the complete positive binding path.
    assert bind()[1] == implementations
    return {'dictionary': arrays[0]['dictionary'], 'const_parameters': arrays[0]['const_parameters'],
            'controls': checked}


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: trait_const_binding_controls.py VERIFICATION_DIR')
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
