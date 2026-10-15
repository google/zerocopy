# Copyright 2026 The Fuchsia Authors
# SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

"""Challenge standard-transmute endpoint admission and compiled providers.

Compiler mutations stay in memory. Lean mutations affect only a disposable
project and are restored and rebuilt. No invalid Rust execution is performed.
"""

import argparse
import copy
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'verification/aeneas'))
import admission
import toolchain


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def admission_controls(work, evidence):
    registry = json.loads((ROOT / 'verification/aeneas/external.json').read_text())
    manifest = json.loads((work / 'bindings.json').read_text())
    laws = [row['rust'] for row in manifest['trait_laws']]
    owner = 'zerocopy::util::owned_transmute::to_bytes'
    for stage, filename in [('before', 'zerocopy.before.ullbc'), ('llbc', 'zerocopy.llbc')]:
        data = json.loads((work / filename).read_text())
        baseline = admission.Admission(data, registry, laws)
        baseline.audit([owner])
        helper = next(f for f in baseline.functions.values()
                      if baseline.name(f['item_meta']['name']) == owner + '_native')
        intrinsic = next(i for i, f in baseline.functions.items()
                         if baseline.name(f['item_meta']['name']) == 'core::intrinsics::transmute')
        calls = [node['Regular'] for node in nodes(helper['body'])
                 if node.get('Regular', {}).get('kind', {}).get('Fun') == intrinsic]
        if len(calls) != 1:
            raise ValueError('Expected one standard call in the actual unannotated helper')
        original = copy.deepcopy(calls[0]['generics']['types'])
        calls[0]['generics']['types'][0] = {'Untagged': {'Scalar': {
            'Integer': {'Unsigned': 'U16'}}}}
        try:
            admission.Admission(data, registry, laws).audit([owner])
        except ValueError as error:
            if 'Unsupported standard transmute instantiation' not in str(error):
                raise ValueError('Endpoint mutation failed outside its intended guard') from error
            evidence.append({'case': stage + '-unsupported-endpoint', 'rejection': str(error)})
        else:
            raise ValueError('Accepted an unsupported original Rust endpoint')
        finally:
            calls[0]['generics']['types'] = original
        for key, bad in [('is_little_endian', False), ('target_pointer_size', 4)]:
            target = data['translated']['target_information'][0]['value']
            old = target[key]
            target[key] = bad
            try:
                admission.Admission(data, registry, laws)
            except ValueError as error:
                if 'little-endian 64-bit target' not in str(error):
                    raise
                evidence.append({'case': stage + '-' + key, 'rejection': str(error)})
            else:
                raise ValueError('Accepted an unsupported original target profile')
            finally:
                target[key] = old


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--runtime', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, required=True)
    args = parser.parse_args()
    work, runtime, output = args.work.resolve(), args.runtime.resolve(), args.evidence.resolve()
    standard = work in [ROOT / 'target/aeneas/verification', ROOT / 'target/aeneas/golden-verification']
    private = (work.name == 'project' and work.parent.parent.name.startswith('control-sandboxes-')
               and work.parent.parent.parent == ROOT / 'target/aeneas'
               and os.environ.get('AENEAS_CONTROL_PROJECT') == str(work)
               and os.environ.get('AENEAS_CONTROL_REPO') == str(ROOT))
    if not (standard or private):
        raise ValueError('Controls require a disposable verification project')
    toolchain.validate(ROOT, runtime)
    output.mkdir(parents=True, exist_ok=False)
    environment = toolchain.runtime_env(runtime)
    environment['LEAN_NUM_THREADS'] = '2'
    results = []
    admission_controls(work, results)
    source = (ROOT / 'verification/aeneas/lean/Check.lean').read_text()
    begin = source.index('-- This closed boundary')
    end = source.index('run_elab do\n')
    probe = work / 'StdTransmuteAuditProbe.lean'
    if probe.exists() or probe.is_symlink():
        raise ValueError('Control probe already belongs to an earlier session')
    probe.write_text('import Lean\nimport Zerocopy.Funs\nopen Lean Elab Command\n' + source[begin:end] +
        'run_elab do\n  let contents ← IO.FS.readFile "bindings.json"\n'
        '  let .ok bindings := Json.parse contents | throwError "Invalid control bindings"\n'
        '  auditStdTransmute bindings\n')
    external, native = work / 'Zerocopy/FunsExternal.lean', work / 'Zerocopy/Funs.lean'
    originals = {external: external.read_text(), native: native.read_text()}
    start = originals[external].index('instance Zerocopy.stdTransmuteU8ToBool :')
    end = originals[external].index('\n-- The additional implicit parameter', start)
    boolean = originals[external][start:end]
    if boolean.count('else forbiddenExecution') != 1:
        raise ValueError('Boolean provider control boundary changed')

    def run(label, command, expected=''):
        log = output / (label + '.log')
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=work, env=environment,
                                    stdout=stream, stderr=subprocess.STDOUT)
        contents = log.read_text()
        results.append({'case': label, 'command': command, 'exit_code': result.returncode,
                        'log': str(log), 'expected_rejection': expected})
        if expected:
            if result.returncode == 0 or expected not in contents:
                raise ValueError(f'{label} did not fail at its intended audit: {log}')
        elif result.returncode:
            raise ValueError(f'{label} failed: {log}')

    build = ['lake', '--old', 'build', '+Zerocopy.Funs:olean']
    audit = ['lake', '--old', 'env', 'lean', '-DwarningAsError=true', probe.name]
    try:
        run('positive-audit', audit)
        for case in ['failure-erasure', 'opaque-provider', 'shadow-provider']:
            for path, text in originals.items():
                path.write_text(text)
            if case == 'failure-erasure':
                external.write_text(originals[external][:start] +
                    boolean.replace('else forbiddenExecution', 'else .ok false') + originals[external][end:])
                rejection = 'changed its whole interpretation'
            elif case == 'opaque-provider':
                external.write_text(originals[external][:start] +
                    'axiom Zerocopy.stdTransmuteU8ToBool : Zerocopy.StdOwnedTransmute U8 Bool\n'
                    'attribute [instance] Zerocopy.stdTransmuteU8ToBool\n' + originals[external][end:])
                rejection = 'must be a definition'
            else:
                external.write_text(originals[external] +
                    '\n@[reducible] def Zerocopy.shadowStdProvider :\n'
                    '    Zerocopy.StdOwnedTransmute U32 (Array U8 4#usize) :=\n'
                    '  Zerocopy.stdTransmuteU32ToBytes\n')
                needle = 'core.intrinsics.transmute (Array Std.U8 4#usize) value'
                if originals[native].count(needle) != 1:
                    raise ValueError('Expected one native primitive call in the unannotated helper')
                native.write_text(originals[native].replace(needle,
                    'core.intrinsics.transmute (Array Std.U8 4#usize) (provider := Zerocopy.shadowStdProvider) value'))
                rejection = 'did not retain its canonical endpoint provider'
            run(case + '-elaboration', build)
            run(case + '-rejection', audit, rejection)
    finally:
        for path, text in originals.items():
            path.write_text(text)
        try:
            run('restored-native-elaboration', build)
            run('restored-positive-audit', audit)
        finally:
            probe.unlink(missing_ok=True)
            (output / 'evidence.json').write_text(json.dumps({'restored': True, 'results': results}, indent=2) + '\n')


if __name__ == '__main__':
    main()
