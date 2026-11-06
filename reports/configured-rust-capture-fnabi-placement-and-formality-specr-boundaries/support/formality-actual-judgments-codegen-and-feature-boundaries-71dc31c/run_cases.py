"""Run each owned observation in a separate process; never reinterpret a panic as rejection."""
import argparse, hashlib, json, os, pathlib, subprocess, time

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--binary', type=pathlib.Path, required=True)
    ap.add_argument('--output', type=pathlib.Path, required=True)
    a = ap.parse_args()
    root = pathlib.Path(__file__).resolve().parent
    binary = a.binary.resolve(strict=True)
    out = a.output.absolute()
    if out.exists() or out.resolve() != out or out.parent.resolve() != out.parent:
        raise ValueError('fresh physical output required')
    out.mkdir()
    results = []
    for case in json.loads((root/'case-plan.json').read_text()):
        name = case['name']
        specimen = root/case['input']
        if sha(specimen) != case['input_sha256']:
            raise ValueError('fixture changed at consumption: '+name)
        case_out = out/name
        argv = [str(binary), case['action'], os.path.relpath(specimen, root),
                os.path.relpath(case_out, root)]
        if case['query']: argv.append(case['query'])
        started = time.monotonic_ns()
        try:
            environment = os.environ.copy()
            environment['TMPDIR'] = str(root/'tmp')
            p = subprocess.run(argv, cwd=root, env=environment, capture_output=True, timeout=30)
        except subprocess.TimeoutExpired as e:
            (out/(name+'.timeout.stdout')).write_bytes(e.stdout or b'')
            (out/(name+'.timeout.stderr')).write_bytes(e.stderr or b'')
            raise RuntimeError('operational timeout; dependent execution stopped: '+name)
        elapsed = time.monotonic_ns()-started
        (out/(name+'.stdout')).write_bytes(p.stdout)
        (out/(name+'.stderr')).write_bytes(p.stderr)
        row = dict(case=case, argv=argv, exit=p.returncode, elapsed_ns=elapsed,
                   stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),
                   stderr_sha256=hashlib.sha256(p.stderr).hexdigest(),
                   expected_status_agrees=p.returncode==case['expected_exit'])
        if case['expected_machine_stdout'] is not None and (case_out/'machine.stdout').exists():
            row['machine_stdout_agrees'] = ((case_out/'machine.stdout').read_bytes()
                                            == case['expected_machine_stdout'].encode())
        results.append(row)
        (out/'partial-results.json').write_text(json.dumps(results, indent=2)+'\n')
        if p.returncode < 0 or p.returncode == 101 or any(x in p.stdout+p.stderr for x in
                [b'panicked at', b'assertion failed', b'Assertion failed']):
            raise RuntimeError('unexpected panic/assertion: '+name+'; stop for diagnosis')
        if p.returncode in [7,8]:
            raise RuntimeError('owned observer operational boundary: '+name)
    report = dict(binary_sha256=sha(binary), cases=results,
                  all_predicted_statuses_agree=all(x['expected_status_agrees'] for x in results),
                  all_observed_machine_outputs_agree=all(x.get('machine_stdout_agrees', True) for x in results),
                  scope='Actual pinned judgments/codegen/vendored-core execution; not a kernel theorem or a rustc frontend proof.')
    (out/'results.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='cases'}, indent=2))

if __name__ == '__main__': main()
