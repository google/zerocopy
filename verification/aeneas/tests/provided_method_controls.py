# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Regression for excluded provided signatures and actual method references.

Usage: provided-method-controls.py CHARON OUTPUT_DIR REPO_ROOT RUST_LIBRARY_DIR
The runtime supplies the pinned Rust executable on PATH. Every output is private
scratch; existing output names reject rather than overwrite another run.
"""

import json
import os
from pathlib import Path
import subprocess
import sys


def check(charon, output, repo, libraries):
    output.mkdir(parents=True, exist_ok=True)
    source = Path(__file__).with_suffix('.rs')
    results = []
    for case in ['keep', 'concrete_keep', 'override_keep', 'required_excluded',
                 'generic_call', 'concrete_call', 'override_call', 'through_hidden', 'inherent_call']:
        prefix = output / case
        if any(Path(str(prefix) + suffix).exists() for suffix in ('.log', '.llbc', '.before.ullbc')):
            raise AssertionError('Compiler regression outputs already exist: ' + str(prefix))
        selected = 'keep' if case == 'required_excluded' else case
        env = os.environ.copy()
        for variable in ['DYLD_LIBRARY_PATH', 'LD_LIBRARY_PATH']:
            env[variable] = str(libraries) + (':' + env[variable] if env.get(variable) else '')
        env['CHARON_ADMISSION_SNAPSHOT'] = str(prefix) + '.before.ullbc'
        options = ['--exclude', 'provided_method_controls::Api::unused',
                   '--exclude', 'provided_method_controls::Api::called']
        if case == 'required_excluded':
            options += ['--exclude', 'provided_method_controls::Api::required']
        if case == 'inherent_call':
            options += ['--exclude', 'provided_method_controls::Plain::plain']
        if case == 'through_hidden':
            options += ['--opaque', 'provided_method_controls::hidden_call']
        command = [str(charon), 'rustc', '--preset=aeneas', '--sysroot', 'default',
                   '--start-from', 'provided_method_controls::' + selected,
                   '--mir', 'promoted', '--no-dedup-serialized-ast', *options,
                   '--dest-file', str(prefix) + '.llbc', '--abort-on-error',
                   '--error-on-warnings', '--', '--crate-name', 'provided_method_controls',
                   '--crate-type', 'lib', str(source)]
        result = subprocess.run(command, env=env, text=True, capture_output=True, cwd=output)
        text = result.stdout + result.stderr
        Path(str(prefix) + '.log').write_text(text)
        record = {'case': case, 'command': command, 'exit_code': result.returncode}
        results.append(record)
        if case in ['generic_call', 'concrete_call', 'override_call']:
            if result.returncode == 0 or 'referenced excluded provided trait method' not in text:
                raise AssertionError('Excluded method reference was accepted or rejected for the wrong reason: ' + case)
            continue
        if result.returncode != 0:
            raise AssertionError('Malformed positive extraction: ' + case + '\n' + text)
        for suffix in ('.llbc', '.before.ullbc'):
            data = json.loads(Path(str(prefix) + suffix).read_text())
            if data.get('has_errors') is not False:
                raise AssertionError('Extraction reported errors: ' + case + suffix)
            crate = data['translated']
            if case == 'inherent_call':
                # This fix governs provided trait slots; an excluded inherent
                # method retains upstream extraction behavior and is not admitted.
                continue
            traits = {t['def_id']: t for t in crate['trait_decls'] if t}
            names = {i: t['item_meta']['name'][-1].get('Ident', [None])[0]
                     for i, t in traits.items()}
            if 'OnlyUnusedDependency' in names.values():
                raise AssertionError('Unused provided signature imported its dependency')
            api = [t for t in traits.values() if names[t['def_id']] == 'Api']
            if len(api) != 1:
                raise AssertionError('Missing exact Api declaration')
            methods = api[0]['methods']
            slots = [(i, m) for i, m in enumerate(methods) if m is not None]
            if len(slots) != 1 or slots[0][0] != 1:
                raise AssertionError('Required original method slot was lost or renumbered')
            method = slots[0][1]
            if (method['skip_binder']['name'] != 'required'
                    or method['kind'] != {'TraitMethod': [api[0]['def_id'], 1]}):
                raise AssertionError('Required method changed compiler identity')
            bounds = method['params']['trait_clauses']
            if not any(names[b['trait_']['skip_binder']['id']] == 'RequiredDependency' for b in bounds):
                raise AssertionError('Required method signature lost its original bound')
            if case == 'through_hidden':
                sys.path.insert(0, str(repo / 'verification/aeneas'))
                import admission
                hidden = next(f for f in crate['fun_decls'] if f and
                              f['item_meta']['name'][-1].get('Ident') == ['hidden_call', 0])
                if hidden['body'] != 'Opaque':
                    raise AssertionError('Opaque-helper control did not exercise an opaque body')
                # Exercise the existing body-boundary guard on the actual emitted record.
                # This unit test intentionally does not claim whole-profile admission;
                # the production profile separately rejects this extra opaque selection.
                audit = admission.Admission.__new__(admission.Admission)
                audit.crate = crate
                audit.functions = {f['def_id']: f for f in crate['fun_decls'] if f}
                audit.types = {t['def_id']: t for t in crate['type_decls'] if t}
                audit.registry = []
                audit.visited = {}
                audit.checked_types = set()
                audit.before = suffix == '.before.ullbc'
                try:
                    audit.visit(hidden['def_id'])
                except ValueError as error:
                    if str(error) != 'No reviewed interpretation for provided_method_controls::hidden_call':
                        raise AssertionError('Unintended opaque boundary rejection: ' + str(error)) from error
                else:
                    raise AssertionError('Unreviewed opaque helper was accepted')
    return results


if __name__ == '__main__':
    if len(sys.argv) != 5:
        raise SystemExit(__doc__)
    print(json.dumps(check(*(Path(arg).resolve() for arg in sys.argv[1:])), indent=2))
