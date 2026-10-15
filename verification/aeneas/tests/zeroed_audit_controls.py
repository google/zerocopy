# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Challenge zeroed's compiled interpretation, provider, and source premises.

Only a disposable generated project is mutated. Every native mutant must first
compile; rejection must then come from its intended audit diagnostic. Compiler
snapshots remain unchanged, and no invalid Rust execution is performed.
"""

import argparse
import copy
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'verification/aeneas'))
import toolchain


PROBE = '''import ZeroedAudit
open Lean Elab
run_elab do
  let contents ← IO.FS.readFile "bindings.json"
  let .ok bindings := Json.parse contents | throwError "Invalid control bindings"
  auditZeroed bindings
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--runtime', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, required=True)
    args = parser.parse_args()
    work = args.work.resolve()
    runtime = args.runtime.resolve()
    output = args.evidence.resolve()
    standard = work in [ROOT / 'target/aeneas/verification',
                        ROOT / 'target/aeneas/golden-verification']
    private = (work.name == 'project'
               and work.parent.parent.name.startswith('control-sandboxes-')
               and work.parent.parent.parent == ROOT / 'target/aeneas'
               and os.environ.get('AENEAS_CONTROL_PROJECT') == str(work)
               and os.environ.get('AENEAS_CONTROL_REPO') == str(ROOT))
    if not (standard or private):
        raise ValueError('Controls require a disposable verification project')
    toolchain.validate(ROOT, runtime)
    environment = toolchain.runtime_env(runtime)
    environment['LEAN_NUM_THREADS'] = '2'
    output.mkdir(parents=True, exist_ok=False)
    probe = work / 'ZeroedAuditProbe.lean'
    if probe.exists() or probe.is_symlink():
        raise ValueError('Zeroed audit probe already belongs to an earlier session')
    external = work / 'Zerocopy/FunsExternal.lean'
    native = work / 'Zerocopy/Funs.lean'
    bindings = work / 'bindings.json'
    originals = {path: path.read_bytes() for path in (external, native, bindings)}
    manifest = json.loads(originals[bindings])
    owner = 'zerocopy::FromZeros::new_zeroed'
    entry = manifest['bindings'][owner]
    if (entry['raw'] != 'Zerocopy.FromZeros.new_zeroed.default'
            or entry['erased_self_bound']['rust'] != 'zerocopy::FromZeros'):
        raise ValueError('Zeroed controls require the actual default and erased Self owner')
    stages = manifest['admission']['stages']
    for stage in ('before', 'llbc'):
        calls = [row for row in stages[stage]['calls']
                 if row.get('callee') == 'core::mem::zeroed']
        if (len(calls) != 1 or calls[0]['caller'] != owner
                or calls[0]['type_arguments'] != ['T0']
                or not isinstance(calls[0]['caller_def_id'], int)):
            raise ValueError('Zeroed controls require the actual original generic call')
    results = []
    restored = False

    def run(label, argv, expected='', *, fresh=False):
        log = output / (label + '.log')
        command = [sys.executable, '-B', str(ROOT / 'verification/aeneas/control_runner.py'),
                   'command']
        if fresh:
            command.append('--fresh')
        command.extend([str(output / 'commands'), '--', *argv])
        with log.open('wb') as stream:
            result = subprocess.run(command, cwd=work, env=environment,
                                    stdout=stream, stderr=subprocess.STDOUT)
        diagnostic = log.read_text(errors='replace')
        results.append({'case': label, 'command': command,
                        'exit_code': result.returncode, 'log': str(log),
                        'expected_rejection': expected})
        if expected:
            if (result.returncode != 1 or expected not in diagnostic
                    or re.search(r'error(?:\([^)]*\))?:', diagnostic) is None):
                raise ValueError(f'{label} did not fail at its intended audit: {log}')
        elif result.returncode != 0:
            raise ValueError(f'{label} failed: {log}')

    build = ['lake', '--old', 'build', '+Zerocopy.FunsExternal',
             '+Zerocopy.Funs', '+ZeroedAudit']
    audit = ['lake', '--old', 'env', 'lean', '-DwarningAsError=true', probe.name]
    required = ['lake', '--old', 'build', '+Required']
    full_audit = ['lake', '--old', 'env', 'lean', '-DwarningAsError=true', 'Check.lean']

    def restore_sources():
        for path, original in originals.items():
            if path.read_bytes() != original:
                path.write_bytes(original)

    def restore_build(label):
        restore_sources()
        run(label + '-elaboration', build, fresh=True)
        run(label + '-audit', audit)

    try:
        with probe.open('x') as stream:
            stream.write(PROBE)
        run('positive-native-elaboration', build, fresh=True)
        run('positive-audit', audit)
        run('positive-required-elaboration', required, fresh=True)
        run('positive-enclosing-premise-audit', full_audit)

        text = originals[external].decode()
        signature = ('noncomputable def core.mem.zeroed (T : Type) '
                     '[model : AeneasSpecs.RustModel T] : Result T :=\n')
        before = signature + '  model.zeroedResult\n'
        after = signature + '''  match model.representation with
  | none => .fail .undef
  | some decoder => Result.ofOption
      (decoder.run (List.replicate decoder.byteSize (Rust.Storage.AMByte.init 0))) .undef
'''
        if text.count(before) != 1:
            raise ValueError('Zeroed interpretation control boundary changed')
        external.write_text(text.replace(before, after))
        run('missing-model-guard-elaboration', build, fresh=True)
        run('missing-model-guard-rejection', audit,
            'core.mem.zeroed changed its full signature or body')
        restore_build('restored-model-guard')

        text = originals[native].decode()
        before = '  core.mem.zeroed Self\n'
        after = '''  core.mem.zeroed Self (model := {
    Model := AeneasSpecs.ModelOf Self,
    decode := fun _ => none,
    storage := (inferInstance : AeneasSpecs.RustModel Self).storage })
'''
        if text.count(before) != 1:
            raise ValueError('Zeroed native default control boundary changed')
        native.write_text(text.replace(before, after))
        run('replaced-provider-elaboration', build, fresh=True)
        run('replaced-provider-rejection', audit,
            'changed its original type or retained provider')
        restore_build('restored-provider')
        run('restored-provider-required-elaboration', required, fresh=True)

        mutant = copy.deepcopy(manifest)
        calls = mutant['admission']['stages']['llbc']['calls']
        next(row for row in calls if row.get('callee') == 'core::mem::zeroed')[
            'type_arguments'] = ['T1']
        bindings.write_text(json.dumps(mutant, indent=2) + '\n')
        run('lowered-endpoint-rejection', audit,
            'Zeroed changed original Rust type arguments, ownership, or multiplicity')
        restore_sources()
        run('restored-endpoint-audit', audit)

        mutant = copy.deepcopy(manifest)
        mutant['bindings'][owner]['erased_self_bound'] = None
        bindings.write_text(json.dumps(mutant, indent=2) + '\n')
        run('vanished-enclosing-premise-rejection', full_audit,
            'Unexpected enclosing trait premise on Zerocopy.FromZeros.new_zeroed.default')
        restore_sources()
        run('restored-enclosing-premise-audit', full_audit)
    finally:
        restore_sources()
        try:
            run('restored-native-elaboration', build, fresh=True)
            run('restored-positive-audit', audit)
            run('restored-required-elaboration', required, fresh=True)
            run('restored-positive-full-audit', full_audit)
            restored = True
        finally:
            probe.unlink(missing_ok=True)
            (output / 'evidence.json').write_text(json.dumps(
                {'restored': restored, 'results': results}, indent=2) + '\n')


if __name__ == '__main__':
    main()
