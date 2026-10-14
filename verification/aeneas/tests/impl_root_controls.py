# SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Native regression for exact compiler-origin impl roots.

Usage: impl_root_controls.py CHARON OUTPUT_DIR REPO_ROOT RUST_LIBRARY_DIR
Outputs reject reuse. AENEAS_TOOLCHAIN_DIR selects the native reader when it is
not next to CHARON. Neither AST options nor source are altered before Aeneas.
"""

import json
import os
from pathlib import Path
import subprocess
import sys


def check(charon, output, repo, libraries, crlf=False):
    output.mkdir(parents=True, exist_ok=True)
    source = output / 'impl_root_controls.rs'
    if source.exists():
        raise AssertionError('Compiler regression source already exists')
    fixture = Path(__file__).with_suffix('.rs').read_bytes()
    source.write_bytes(fixture.replace(b'\n', b'\r\n') if crlf else fixture)
    data = source.read_bytes()

    def owner(text):
        begin = data.index(text.encode())
        brace = data.index(b'{', begin)
        depth, end = 1, brace + 1
        while depth:
            depth += (data[end] == 123) - (data[end] == 125)
            end += 1
        return f'{source.name}:{begin}:{end}'

    array = owner('unsafe impl<T')
    invocation = data.index(b'generated!();')
    both = data.index(b'two!();')
    header_end = data.index(b'{', int(array.split(':')[-2]))
    cases = [
        ('array', [array], None),
        ('duplicate', [array, array], 'duplicate source-owner root'),
        ('stale', [array.rsplit(':', 1)[0] + ':' + str(int(array.rsplit(':', 1)[1]) + 1)], 'matched 0 local owners'),
        ('header_only', [array.rsplit(':', 1)[0] + ':' + str(header_end)], 'matched 0 local owners'),
        ('function', [owner('fn ignored_pointer')], 'requires a non-expanded positive trait impl'),
        ('inherent', [owner('impl Inherent')], 'requires a non-expanded positive trait impl'),
        ('negative', [owner('impl !Auto')], 'requires a non-expanded positive trait impl'),
        ('macro_template', [owner('impl MacroTrait')], 'requires a non-expanded positive trait impl'),
        ('macro_call', [f'{source.name}:{invocation}:{invocation + len(b"generated!()")}'], 'requires a non-expanded positive trait impl'),
        ('ambiguous_macro', [f'{source.name}:{both}:{both + len(b"two!()")}'], 'matched 2 local owners'),
        ('absent', [array.replace(source.name, 'foreign.rs')], 'matched 0 local owners'),
        ('ordinary_errors', [array.replace(source.name, 'foreign.rs')], 'matched 0 local owners'),
        ('absolute', [str(output) + '/' + array], 'invalid source-owner root'),
        ('path_alias', [array.replace(source.name, './' + source.name)], 'invalid source-owner root'),
        ('malformed', [source.name + ':invalid:3'], 'invalid source-owner root'),
    ]
    if crlf:
        cases = cases[:1]
    env = os.environ.copy()
    tools = Path(env.get('AENEAS_TOOLCHAIN_DIR', charon.parent))
    for variable in ['DYLD_LIBRARY_PATH', 'LD_LIBRARY_PATH']:
        env[variable] = str(libraries) + ':' + str(tools / 'libs') + (':' + env[variable] if env.get(variable) else '')
    results = []
    for case, selectors, failure in cases:
        prefix = output / case
        if any(Path(str(prefix) + suffix).exists() for suffix in ('.log', '.llbc', '.before.ullbc')):
            raise AssertionError('Compiler regression outputs already exist: ' + str(prefix))
        arguments = []
        for selector in selectors:
            arguments += ['--start-from', '@span:' + selector]
        env['CHARON_ADMISSION_SNAPSHOT'] = str(prefix) + '.before.ullbc'
        command = [str(charon), 'rustc', '--preset=aeneas', '--sysroot', 'default',
                   *arguments, '--exclude', 'impl_root_controls::IntoBytes::provided',
                   '--mir', 'promoted', '--no-dedup-serialized-ast', '--dest-file',
                   str(prefix) + '.llbc', '--abort-on-error', '--error-on-warnings',
                   '--', '--crate-name', 'impl_root_controls', '--crate-type', 'lib', str(source)]
        if case == 'ordinary_errors':
            command = [arg for arg in command if arg not in ['--abort-on-error', '--error-on-warnings']]
        result = subprocess.run(command, cwd=output, env=env, text=True, capture_output=True)
        text = result.stdout + result.stderr
        Path(str(prefix) + '.log').write_text(text)
        record = {'case': case, 'command': command, 'exit_code': result.returncode}
        results.append(record)
        if failure:
            if result.returncode == 0 or failure not in text:
                raise AssertionError('Accepted invalid owner or rejected for another reason: ' + case + '\n' + text)
            if Path(str(prefix) + '.llbc').exists():
                raise AssertionError('Failed owner emitted a usable final AST: ' + case)
            continue
        if result.returncode != 0:
            raise AssertionError('Caller-free impl extraction failed:\n' + text)
        impls = []
        for original, suffix in [(True, '.before.ullbc'), (False, '.llbc')]:
            payload = json.loads(Path(str(prefix) + suffix).read_text())
            if payload.get('has_errors') is not False:
                raise AssertionError('Extraction reported errors')
            crate = payload['translated']
            if crate['options']['start_from'] != ['@span:' + array]:
                raise AssertionError('Exact owner selector was not recorded')
            local = [i for i in crate['trait_impls'] if i and i['item_meta']['is_local']]
            if len(local) != 1 or not local[0]['item_meta']['started_from']:
                raise AssertionError('Owner root broadened or was missing')
            if any(f and f['item_meta']['started_from'] for f in crate['fun_decls']):
                raise AssertionError('Impl child methods became function roots')
            impl = local[0]
            span = impl['item_meta']['span']['Untagged']
            if span['generated_from_span'] is not None:
                raise AssertionError('Expanded owner was accepted')
            trait = next(t for t in crate['trait_decls'] if t and t['def_id'] == impl['impl_trait']['id'])
            if trait['item_meta']['name'][-1].get('Ident') != ['IntoBytes', 0]:
                raise AssertionError('Wrong native trait identity')
            bound = {'Bound': [0, 0]} if original else {'Free': 0}
            usize = {'Untagged': {'Scalar': {'Integer': {'Unsigned': 'Usize'}}}}
            expected = {'Untagged': {'Array': [{'Untagged': {'TypeVar': bound}},
                         {'Untagged': [{'Var': bound}, usize]}, None]}}
            if impl['impl_trait']['generics']['types'] != [expected]:
                raise AssertionError('Array type or original const identity changed')
            generics = impl['generics']
            if (generics['types'] != [{'index': 0, 'name': 'T', 'variance': 'Unknown'}]
                    or generics['const_generics'] != [{'index': 0, 'name': 'N', 'ty': usize}]):
                raise AssertionError('Original type/usize const telescope changed')
            # The original clause has its own RegionBinder outside the impl binder.
            clause_bound = {'Bound': [1, 0]} if original else {'Free': 0}
            clauses = generics['trait_clauses']
            if (len(clauses) != 1 or clauses[0]['clause_id'] != 0
                    or clauses[0]['trait_']['skip_binder'] != {'id': trait['def_id'], 'generics': {
                        'regions': [], 'types': [{'Untagged': {'TypeVar': clause_bound}}],
                        'const_generics': [], 'trait_refs': []}}):
                raise AssertionError('Input computational dictionary identity changed')
            if len(impl['methods']) != 1 or impl['methods'][0]['kind'] != {'TraitMethod': [trait['def_id'], 0]}:
                raise AssertionError('Required original method identity changed')
            impls.append(impl)
        if (impls[0]['def_id'] != impls[1]['def_id']
                or impls[0]['item_meta']['span'] != impls[1]['item_meta']['span']):
            raise AssertionError('Original/final compiler owner identity changed')
        native = output / 'native'
        native.mkdir()
        command = [str(tools / 'aeneas'), '-backend', 'lean', '-namespace', 'Probe',
                   '-dest', str(native), '-split-files', '-emit-json', '-abort-on-error',
                   '-warnings-as-errors', '-no-progress-bar', '-use-tuple-structs', 'false',
                   str(prefix) + '.llbc']
        result = subprocess.run(command, cwd=output, env=env, text=True, capture_output=True)
        (output / 'aeneas.log').write_text(result.stdout + result.stderr)
        record.update(aeneas_command=command, aeneas_exit_code=result.returncode)
        if result.returncode != 0:
            raise AssertionError('Unaltered owner-root AST failed native emission')
        metadata = json.loads((native / 'translation.json').read_text())
        if (len(metadata['trait_impls']) != 1
                or metadata['trait_impls'][0]['def_id'] != impls[1]['def_id']
                or metadata['trait_impls'][0]['lean_name'] != 'Probe.Array.Insts.Impl_root_controlsIntoBytes'):
            raise AssertionError('Wrong or broadened exact native dictionary mapping')
        record['native_impl'] = metadata['trait_impls'][0]
    (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print('Exact impl root controls passed:', len(results))


if __name__ == '__main__':
    if len(sys.argv) != 5:
        raise SystemExit(__doc__)
    args = [Path(value).resolve() for value in sys.argv[1:]]
    check(*args)
    check(args[0], args[1] / 'crlf', args[2], args[3], crlf=True)
