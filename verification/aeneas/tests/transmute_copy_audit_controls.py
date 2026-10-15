# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Compile byte-copy mutants before challenging their independent binding audit.

Only a private control-runner project may be changed. Providers retain their
original Raw type, so a type error cannot stand in for detecting a replacement
interpretation. Every command has durable evidence; finally restores sources,
rebuilds the original modules, and reruns the original audit.
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

PROBE = '''import NativeProviderAudit
open Lean Elab
run_elab do
  let contents ← IO.FS.readFile "bindings.json"
  let .ok bindings := Json.parse contents | throwError "Invalid control bindings"
  auditNativeProviders bindings
'''
GUARD_PROBE = '''import Zerocopy.Funs
open Aeneas.Std AeneasSpecs Zerocopy
-- Removing the guard also makes its simp arguments unused. Suppress that
-- linter here so only the unproved execution proposition rejects the mutant.
set_option linter.unusedSimpArgs false
example {Src Dst : Type} (source : IntoBytes Src) (destination : FromBytes Dst)
    (src : Src) [RustModel Src] [RustModel Dst] (sourceSize destinationSize : Usize)
    (hs : core.mem.size_of Src = .ok sourceSize)
    (hd : core.mem.size_of Dst = .ok destinationSize)
    (different : sourceSize ≠ destinationSize) :
    util.macro_util.transmute_copy source destination src = .fail .assertionFailure := by
  simp only [util.macro_util.transmute_copy,
    PairPhantomDataPhantomData.Insts.ZerocopyUtilMacro_utilTransmute_copyStaticAssert.ASSERT,
    hs, hd]
  try simp [different, Aeneas.Std.massert]
'''
EXACT_PROVIDER = 'Provider-bearing call changed its exact retained provider'
ENDPOINTS = 'Provider-bearing calls changed original endpoints, owners, or multiplicity'
COPY = 'core::mem::transmute_copy'


def replace_once(text, before, after):
    if text.count(before) != 1:
        raise ValueError('Byte-copy mutation requires one exact source boundary: ' + before)
    return text.replace(before, after)


def changed_provider(raw, field):
    value = 'fun _ => []' if field == 'representationChoice' else 'fun _ => none'
    return ('{ (inferInstance : AeneasSpecs.RustModel (' + raw + ')) with '
            + field + ' := ' + value + ' }')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--runtime', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, required=True)
    args = parser.parse_args()
    work, runtime, output = (path.resolve() for path in
                             (args.work, args.runtime, args.evidence))
    private = (work.name == 'project'
        and work.parent.parent.name.startswith('control-sandboxes-')
        and work.parent.parent.parent == ROOT / 'target/aeneas'
        and os.environ.get('AENEAS_CONTROL_PROJECT') == str(work)
        and os.environ.get('AENEAS_CONTROL_REPO') == str(ROOT))
    if not private:
        raise ValueError('Byte-copy controls require a private control-runner project')
    toolchain.validate(ROOT, runtime)
    environment = toolchain.runtime_env(runtime)
    environment['LEAN_NUM_THREADS'] = '2'
    probe = work / 'TransmuteCopyAuditProbe.lean'
    if probe.exists() or probe.is_symlink():
        raise ValueError('Byte-copy audit probe already belongs to an earlier session')
    external = work / 'Zerocopy/FunsExternal.lean'
    native = work / 'Zerocopy/Funs.lean'
    bindings = work / 'bindings.json'
    originals = {path: path.read_bytes() for path in (external, native, bindings)}
    manifest = json.loads(originals[bindings])
    for rust, raw in [('zerocopy::util::macro_util::transmute_copy',
                       'Zerocopy.util.macro_util.transmute_copy'),
                      ('zerocopy::util::generic_transmute::transmute_copy_caller',
                       'Zerocopy.util.generic_transmute.transmute_copy_caller')]:
        if manifest['bindings'].get(rust, {}).get('raw') != raw:
            raise ValueError('Byte-copy controls require the actual helper and caller roots')
    for stage in ('before', 'llbc'):
        calls = [row for row in manifest['admission']['stages'][stage]['calls']
                 if row.get('callee') == COPY]
        if len(calls) != 1 or calls[0]['type_arguments'] != [
                'core::mem::manually_drop::ManuallyDrop<T0>', 'T1']:
            raise ValueError('Byte-copy controls require the selected original generic endpoints')
    output.mkdir(parents=True, exist_ok=False)
    results, restored = [], False

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
            'exit_code': result.returncode, 'log': str(log), 'expected_rejection': expected})
        if expected:
            if (result.returncode != 1 or expected not in diagnostic or
                    re.search(r'error(?:\([^)]*\))?:', diagnostic) is None):
                raise ValueError(f'{label} did not fail at its intended audit: {log}')
        elif result.returncode != 0:
            raise ValueError(f'{label} failed: {log}')

    build = ['lake', '--old', 'build', '+Zerocopy.FunsExternal',
             '+Zerocopy.Funs', '+NativeProviderAudit']
    audit = ['lake', '--old', 'env', 'lean', '-DwarningAsError=true', probe.name]
    proof = ['lake', '--old', 'build', '+Proofs.GenericTransmute']

    def restore_sources():
        for path, original in originals.items():
            if path.read_bytes() != original:
                path.write_bytes(original)

    def restore_build(label):
        restore_sources()
        run(label + '-elaboration', build, fresh=True)
        run(label + '-audit', audit)

    def compiled_mutant(label, path, before, after, expected):
        path.write_text(replace_once(originals[path].decode(), before, after))
        run(label + '-elaboration', build, fresh=True)
        run(label + '-rejection', audit, expected)
        restore_build('restored-' + label)

    try:
        with probe.open('x') as stream:
            stream.write(PROBE)
        run('positive-elaboration', build, fresh=True)
        run('positive-audit', audit)
        run('positive-guard-proof', proof, fresh=True)
        copy_call = '  core.mem.transmute_copy Dst src1\n'
        for field in ('representationChoice', 'decode'):
            compiled_mutant('copy-source-' + field, native, copy_call,
                '  core.mem.transmute_copy Dst src1 (source := ' +
                changed_provider('core.mem.manually_drop.ManuallyDrop Src', field) + ')\n',
                EXACT_PROVIDER)
        compiled_mutant('copy-destination-decode', native, copy_call,
            '  core.mem.transmute_copy Dst src1 (destination := ' +
            changed_provider('Dst', 'decode') + ')\n', EXACT_PROVIDER)
        # Size queries retain the provider-free ABI interpretation. Swapping
        # their original type arguments challenges the StaticAssert binding.
        compiled_mutant('static-assert-size-endpoints', native,
            '  let i ← core.mem.size_of Src\n  let i1 ← core.mem.size_of Dst\n',
            '  let i ← core.mem.size_of Dst\n  let i1 ← core.mem.size_of Src\n',
            'Provider-bearing call changed an original Rust endpoint')
        compiled_mutant('caller-source-provider', native,
            '  util.macro_util.transmute_copy IntoBytesInst FromBytesInst src\n',
            '  util.macro_util.transmute_copy IntoBytesInst FromBytesInst src\n'
            '    (_nativeModel0 := ' + changed_provider('Src', 'decode') + ')\n', EXACT_PROVIDER)
        constructor = ('def core.mem.manually_drop.ManuallyDrop.new {T : Type} (src : T) :\n'
            '    Result (core.mem.manually_drop.ManuallyDrop T) := .ok ⟨src⟩\n')
        compiled_mutant('constructor-result', external, constructor,
            constructor.replace('(src : T)', '(_src : T)').replace('.ok ⟨src⟩', '.fail .undef'),
            'Byte-copy boundary core.mem.manually_drop.ManuallyDrop.new changed its whole signature or interpretation')
        primitive = '  source.transmuteCopyResult destination src\n'
        primitive_error = ('Byte-copy boundary core.mem.transmute_copy changed its whole '
                           'signature or interpretation')
        signature = ('noncomputable def core.mem.transmute_copy {Src : Type} '
            '(Dst : Type) (src : Src)\n'
            '    [source : AeneasSpecs.RustModel Src] '
            '[destination : AeneasSpecs.RustModel Dst] : Result Dst :=\n')
        failing = (signature.replace('(src : Src)', '(_src : Src)')
            .replace('[source :', '[_source :')
            .replace('[destination :', '[_destination :') + '  .fail .undef\n')
        compiled_mutant('copy-always-undef', external, signature + primitive,
                        failing, primitive_error)
        compiled_mutant('copy-without-mathematical-guards', external, primitive,
            '  match destination.representation with\n'
            '  | none => .fail .undef\n'
            '  | some decoder => Result.ofOption\n'
            '      (decoder.run (source.representationChoice src)) .undef\n', primitive_error)

        # Equal-size success alone cannot detect a removed guard. Compile the
        # mutated helper first, then require the independent unequal-size proof
        # to fail. Its theorem promises assertionFailure, distinct from UB.
        guard = ('  let b ←\n'
            '    PairPhantomDataPhantomData.Insts.ZerocopyUtilMacro_utilTransmute_copyStaticAssert.ASSERT\n'
            '      Src\n      Dst\n  massert b\n')
        probe.write_text(GUARD_PROBE)
        run('positive-size-guard-proposition', audit)
        native.write_text(replace_once(originals[native].decode(), guard, ''))
        run('missing-size-guard-elaboration', build, fresh=True)
        run('missing-size-guard-proof-rejection', audit, 'unsolved goals')
        probe.write_text(PROBE)
        restore_build('restored-size-guard')
        run('restored-size-guard-proof', proof, fresh=True)

        mutant = copy.deepcopy(manifest)
        next(row for row in mutant['admission']['stages']['llbc']['calls']
             if row.get('callee') == COPY)['type_arguments'].reverse()
        bindings.write_text(json.dumps(mutant, indent=2) + '\n')
        run('lowered-endpoint-rejection', audit, ENDPOINTS)
        restore_sources()
        run('restored-lowered-endpoint-audit', audit)

        mutant = copy.deepcopy(manifest)
        for stage in ('before', 'llbc'):
            next(row for row in mutant['admission']['stages'][stage]['calls']
                 if row.get('callee') == COPY)['type_arguments'] = [
                     'core::mem::manually_drop::ManuallyDrop<T1>', 'T0']
        bindings.write_text(json.dumps(mutant, indent=2) + '\n')
        run('both-endpoints-rejection', audit,
            'Provider-bearing call changed an original Rust endpoint')
        restore_sources()
        run('restored-both-endpoints-audit', audit)

        for kind in ('copy', 'global'):
            mutant = copy.deepcopy(manifest)
            for stage in ('before', 'llbc'):
                rows = mutant['admission']['stages'][stage]['calls']
                matches = [row for row in rows if (row.get('callee') == COPY
                           if kind == 'copy' else row.get('kind') == 'global' and
                           'transmute_copy' in row.get('caller', ''))]
                if len(matches) != 1:
                    raise ValueError('Expected one original call witness for ' + kind)
                rows.remove(matches[0])
            bindings.write_text(json.dumps(mutant, indent=2) + '\n')
            run('missing-' + kind + '-witness-rejection', audit,
                'Unexpected provider-bearing native call')
            restore_sources()
            run('restored-' + kind + '-witness-audit', audit)
    finally:
        restore_sources()
        if probe.exists():
            probe.write_text(PROBE)
        try:
            run('restored-positive-elaboration', build, fresh=True)
            run('restored-positive-audit', audit)
            run('restored-positive-guard-proof', proof, fresh=True)
            restored = True
        finally:
            probe.unlink(missing_ok=True)
            (output / 'evidence.json').write_text(json.dumps(
                {'restored': restored, 'results': results}, indent=2) + '\n')


if __name__ == '__main__':
    main()
