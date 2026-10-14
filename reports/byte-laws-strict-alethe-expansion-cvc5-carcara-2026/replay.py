"""Replay fixed whole byte-law certificates with explicitly selected tools.

This fixture is not a general secure validator against malicious same-user
processes. Independent review of root-locks.json and the predicate map is part
of binding the intended source/claim. The translator/reconstructor are untrusted.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

from countermodels import decode_and_check, witness_source
from reconstruct import produce
from translate import translate


WHOLE = ['into_bytes', 'byte_write', 'bool_validate', 'array_validate']
FALSE = ['missing_initialization', 'alias_frame', 'bool_two', 'missing_stability',
         'array_index_omission']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def accepted(exit_code, stdout):
    return exit_code == 0 and stdout == b'valid\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cvc5', type=Path, required=True)
    parser.add_argument('--carcara', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--samples', type=int, choices=[1, 3], default=3)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    out = args.output.absolute()
    if out.exists() or out.resolve() != out or out.parent.resolve() != out.parent:
        raise ValueError('output must be a fresh physical child of an existing physical parent')
    tools = {name: getattr(args, name).resolve(strict=True) for name in ['cvc5', 'carcara', 'lean']}
    locks = json.loads((source / 'root-locks.json').read_text())['cases']
    tool_locks = json.loads((source / 'tool-locks.json').read_text())
    for name, binary in tools.items():
        if sha(binary) != tool_locks[name]['binary_sha256']:
            raise ValueError('selected tool bytes differ from observed pinned tool: ' + name)
    lean_home = tools['lean'].parent.parent
    for name, path in [('lean_shared', lean_home / 'lib/lean/libleanshared.dylib'),
                       ('lean_Init', lean_home / 'lib/lean/Init.olean')]:
        if sha(path) != tool_locks[name]['sha256']:
            raise ValueError('selected Lean dependency differs from pin: ' + name)
    for case, lock in locks.items():
        if sha(source / lock['smt_file']) != lock['smt_sha256']:
            raise ValueError('independent root-lock mismatch: ' + case)
    if sha(source / 'ByteLaws.lean') != tool_locks['ByteLaws']['sha256']:
        raise ValueError('finite semantic fixture changed')
    out.mkdir()
    rows = []

    def run(binary_name, extra, stem):
        # Reobserve the executable before every consuming invocation.
        if sha(tools[binary_name]) != tool_locks[binary_name]['binary_sha256']:
            raise ValueError('tool changed at consumption')
        environment = os.environ.copy()
        environment['LEAN_PATH'] = str(out)
        started = time.monotonic_ns()
        try:
            # Relative specimen paths keep diagnostics portable; the caller's
            # explicit executable identity is still the pinned absolute binary.
            arguments = [os.path.relpath(value, out) if isinstance(value, Path)
                         else str(value) for value in extra]
            p = subprocess.run([str(tools[binary_name])] + arguments,
                               cwd=out, env=environment, capture_output=True, timeout=30)
            status, stdout, stderr = p.returncode, p.stdout, p.stderr
            timeout = False
        except subprocess.TimeoutExpired as failure:
            status, stdout, stderr = None, failure.stdout or b'', failure.stderr or b''
            timeout = True
        row = {'tool': binary_name, 'exit': status, 'timeout': timeout,
               'elapsed_ns': time.monotonic_ns() - started,
               'stdout_bytes': len(stdout), 'stderr_bytes': len(stderr)}
        (out / (stem + '.stdout')).write_bytes(stdout)
        (out / (stem + '.stderr')).write_bytes(stderr)
        (out / (stem + '.json')).write_text(json.dumps(row, indent=2) + '\n')
        rows.append({'capture': stem, **row})
        if timeout or status is None or status < 0:
            raise RuntimeError('operational stop; inspect retained capture: ' + stem)
        if any(marker in stdout + stderr for marker in
               [b'panicked at', b'Assertion failed', b'assertion failed']):
            raise RuntimeError('unexpected panic/assertion; dependent work stopped: ' + stem)
        return status, stdout, stderr

    def root(case):
        path = source / locks[case]['smt_file']
        if sha(path) != locks[case]['smt_sha256']:
            raise ValueError('root changed at consumption: ' + case)
        return path

    def check(proof, case, stem, want):
        status, stdout, _ = run('carcara', ['--no-color', 'check', proof, root(case)], stem)
        actual = accepted(status, stdout)
        result = {'capture': stem, 'case': case, 'proof_sha256': sha(proof),
                  'root_sha256': sha(root(case)), 'exit': status,
                  'verdict': stdout.decode(errors='replace').strip(), 'accepted': actual}
        if actual != want:
            raise RuntimeError('unexpected acceptance result; inspect capture: ' + stem)
        return result

    matrix = []
    for sample in range(args.samples):
        for case in WHOLE + ['wrong_narrow_domain']:
            label = f'{case}.{sample}'
            original = root(case)
            status, raw, _ = run('cvc5', ['--proof-format-mode=alethe',
                                        '--proof-granularity=dsl-rewrite-strict', original],
                                 label + '.cvc5.generate')
            if status != 0 or not raw.startswith(b'unsat\n'):
                raise RuntimeError('unexpected cvc5 result for fixed valid root')
            raw_proof = out / (label + '.raw.alethe')
            raw_proof.write_bytes(raw[len(b'unsat\n'):])
            raw_result = check(raw_proof, case, label + '.raw.check', case == 'into_bytes')
            before = time.monotonic_ns()
            translated, counts = translate(raw_proof.read_text())
            translation_ns = time.monotonic_ns() - before
            proof = out / (label + '.translated.alethe')
            proof.write_text(translated)
            result = check(proof, case, label + '.translated.check', True)
            result.update(sample=sample, route='actual cvc5 -> untrusted local expansion -> strict Carcara',
                          expanded_rewrite_counts=counts, translation_ns=translation_ns,
                          proof_bytes=proof.stat().st_size, raw_export=raw_result)
            matrix.append(result)
            if sample == 0:
                reconstructed = out / (case + '.reconstructed.alethe')
                reconstructed.write_text(produce(case, original.read_text()))
                matrix.append({**check(reconstructed, case, case + '.reconstructed.check', True),
                               'route': 'independent bounded reconstruction diagnostic'})

    controls = []
    for good, bad in [('into_bytes', 'missing_initialization'), ('byte_write', 'alias_frame'),
                      ('bool_validate', 'bool_two'), ('bool_validate', 'missing_stability'),
                      ('array_validate', 'array_index_omission'),
                      ('wrong_narrow_domain', 'bool_two')]:
        proof = out / (good + '.0.translated.alethe')
        controls.append(check(proof, bad, good + '.attached-to.' + bad, False))
    valid = (out / 'byte_write.0.translated.alethe').read_text()
    holey = out / 'holey-write.alethe'
    holey.write_text(valid.replace(':rule arrays_idx)', ':rule hole)', 1))
    controls.append(check(holey, 'byte_write', 'holey-write.check', False))
    if controls[-1]['verdict'] != 'holey' or controls[-1]['exit'] != 0:
        raise RuntimeError('holey regression must exercise exit-zero rejection')
    corrupted = out / 'corrupt-write.alethe'
    corrupted.write_text(valid.replace('(step t1 (cl @p_14)', '(step t1 (cl false)', 1))
    if corrupted.read_text() == valid:
        raise ValueError('bounded corruption fixture no longer matches actual producer')
    controls.append(check(corrupted, 'byte_write', 'corrupt-write.check', False))
    forged = out / 'forged-assumption.alethe'
    forged.write_text(valid.replace('(assume a0 ', '(assume forged false)\n(assume a0 ', 1))
    controls.append(check(forged, 'byte_write', 'forged-assumption.check', False))
    projection = source / 'projection-only.alethe'
    controls.append(check(projection, 'byte_write', 'projection-attached-to-whole.check', False))
    # The expected full-domain identity is independent of what a producer returns.
    domain_control = {'expected_full_root': locks['bool_two']['smt_sha256'],
                      'proposed_narrow_root': sha(root('wrong_narrow_domain')),
                      'admitted': sha(root('wrong_narrow_domain')) == locks['bool_two']['smt_sha256']}
    if domain_control['admitted']:
        raise RuntimeError('narrowed domain unexpectedly admitted as full domain')

    models = {}
    countermodels = []
    for case in FALSE:
        status, raw, _ = run('cvc5', [root(case)], case + '.countermodel')
        if status != 0:
            raise RuntimeError('SAT query operational failure')
        environment, count = decode_and_check(raw.decode(), root(case).read_text())
        models[case] = environment
        countermodels.append({'case': case, 'valuation': environment,
                              'all_exact_root_assertions_true': True, 'assertions_evaluated': count,
                              'solver_output_sha256': hashlib.sha256(raw).hexdigest()})
    (out / 'ByteLaws.lean').write_bytes((source / 'ByteLaws.lean').read_bytes())
    status, stdout, stderr = run('lean', ['-o', out / 'ByteLaws.olean', out / 'ByteLaws.lean'], 'finite-model')
    if status != 0 or stderr or b'sorryAx' in stdout:
        raise RuntimeError('finite semantic fixture not cleanly checked')
    (out / 'SolverWitnesses.lean').write_text(witness_source(models))
    status, stdout, stderr = run('lean', [out / 'SolverWitnesses.lean'], 'countermodel-lean')
    if status != 0 or stderr or b'sorryAx' in stdout:
        raise RuntimeError('countermodel refutations not cleanly checked')
    report = {'whole_law_cases': WHOLE, 'samples': args.samples, 'matrix': matrix,
              'rejection_controls': controls, 'domain_identity_control': domain_control,
              'countermodels': countermodels, 'phases': rows,
              'acceptance_policy': 'exit == 0 AND stdout bytes exactly valid newline',
              'frontier': 'Native checker, root binding, fixture quotation, SMT theory and Rust correspondence remain explicit premises.'}
    (out / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'all_four_original_whole_laws_strictly_accepted': True,
                      'translated_checks': args.samples * 5,
                      'rejection_controls': len(controls), 'SAT_to_Lean_refutations': len(models)}, indent=2))


if __name__ == '__main__':
    main()
