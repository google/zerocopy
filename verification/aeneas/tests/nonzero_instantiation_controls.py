# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Challenge the original Rust identities in a real pinned extraction.

The lifted inner carrier is an alias in Lean. Changing its Rust identity must
still reject admission, independently of the model's native T = Usize guard.
Mutations stay in memory and never execute invalid Rust or rewrite snapshots.
"""
import copy
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'verification/aeneas'))
import admission


def dictionaries(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from dictionaries(child)
    elif isinstance(value, list):
        for child in value:
            yield from dictionaries(child)


def main(work):
    registry = json.loads((ROOT / 'verification/aeneas/external.json').read_text())
    manifest = json.loads((work / 'bindings.json').read_text())
    laws = [row['rust'] for row in manifest['trait_laws']]
    root = 'zerocopy::trait_checks::divide_by_unaligned'
    for stage, filename in [('before', 'zerocopy.before.ullbc'), ('llbc', 'zerocopy.llbc')]:
        data = json.loads((work / filename).read_text())
        baseline = admission.Admission(data, registry, laws)
        baseline.audit([root])
        # Match compiler paths without interpreting unrelated signature-only
        # carriers. The positive root audit already checks its actual callee.
        constructors = {index for index, function in baseline.functions.items()
                        if function['item_meta']['name'][-1] == {'Ident': ['new_unchecked', 0]}}
        owner = next(function for function in baseline.functions.values()
                     if function['item_meta']['name'] == [{'Ident': [part, 0]} for part in root.split('::')])
        calls = []
        for node in dictionaries(owner['body']):
            function = node.get('func', {}).get('Regular', {})
            if function.get('kind', {}).get('Fun') in constructors:
                calls.append(function)
        if len(calls) != 1:
            raise ValueError(f'{stage}: expected exactly one actual constructor call')
        original = calls[0]['generics']['types']
        original_values = copy.deepcopy(original)
        expected_count = 1 if stage == 'before' else 2
        if len(original) != expected_count:
            raise ValueError(f'{stage}: constructor generic prefix changed')
        mutations = [('integer identity', 0, {'Untagged': {'Scalar': {
            'Integer': {'Unsigned': 'U8'}}}})]
        if stage == 'llbc':
            # Both carriers lower to Usize, but their original Rust identities
            # differ. The guarded native definition cannot detect this change.
            mutations.append(('lifted inner identity', 1, copy.deepcopy(original[0])))
        for label, index, replacement in mutations:
            original[index] = replacement
            try:
                admission.Admission(data, registry, laws).audit([root])
            except ValueError as error:
                if 'Unsupported NonZero::new_unchecked instantiation' not in str(error):
                    raise ValueError(f'{stage}: {label} failed outside its intended guard') from error
                print(f'Confirmed: {stage} rejects changed {label}')
            else:
                raise ValueError(f'{stage}: accepted changed {label}')
            finally:
                original[index] = copy.deepcopy(original_values[index])


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
