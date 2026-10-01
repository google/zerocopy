#!/usr/bin/env python3
"""Guarded, serial Lean batch comparison. No Lake, network, or server."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
TOOLS = {
    'old': Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean'),
    'new': Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'),
}
TOOL_SHA = {
    'old': 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997',
    'new': '1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554',
}
CASES = ('a', 'b', 'c', 'd', 'e')
FORMAT_OPTIONS = {
    'default-text': ((), False),
    'default-json': ((), True),
    'width10-off': (('pp.oneline=false', 'format.width=10'), True),
    'width120-off': (('pp.oneline=false', 'format.width=120'), True),
    'width10-on': (('pp.oneline=true', 'format.width=10'), True),
    'width120-on': (('pp.oneline=true', 'format.width=120'), True),
    'indent2': (('format.indent=2',), True),
    'indent8': (('format.indent=8',), True),
    'unicode-fun-default': (('pp.unicode=true', 'pp.unicode.fun=false'), True),
    'ascii-fun-default': (('pp.unicode=false', 'pp.unicode.fun=false'), True),
    'unicode-fun-arrow': (('pp.unicode=true', 'pp.unicode.fun=true'), True),
    'ascii-fun-arrow': (('pp.unicode=false', 'pp.unicode.fun=true'), True),
    'mvars-false': (('pp.mvars.anonymous=false',), True),
    'mvars-true': (('pp.mvars.anonymous=true',), True),
    'fvars-false': (('pp.fvars.anonymous=false',), True),
    'fvars-true': (('pp.fvars.anonymous=true',), True),
    'endpos-false-text': (('printMessageEndPos=false',), False),
    'endpos-false-json': (('printMessageEndPos=false',), True),
    'endpos-true-text': (('printMessageEndPos=true',), False),
    'endpos-true-json': (('printMessageEndPos=true',), True),
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def admission():
    vm = subprocess.check_output(['vm_stat'], text=True)
    page = int(re.search(r'page size of (\d+) bytes', vm).group(1))
    pages = {name: int(re.search(r'Pages ' + name + r':\s+(\d+)', vm).group(1))
             for name in ('free', 'inactive', 'speculative')}
    total = int(subprocess.check_output(['sysctl', '-n', 'hw.memsize'], text=True))
    pct = 100 * page * sum(pages.values()) / total
    disk = shutil.disk_usage(ROOT).free
    owned = sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())
    rec = {'page_bytes': page, 'pages': pages, 'memory_bytes': total,
           'reclaimable_percent': pct, 'disk_free_bytes': disk,
           'owned_bytes': owned}
    if pct <= 20 or disk <= 1_073_741_824 or owned >= 100_000_000:
        raise RuntimeError(f'resource admission failed: {rec}')
    return rec

def guarded(argv, env=None):
    gate = admission()
    start = time.monotonic()
    proc = subprocess.Popen(argv, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    peak_rss_kib = 0
    while True:
        try:
            stdout, stderr = proc.communicate(timeout=.05)
            break
        except subprocess.TimeoutExpired:
            elapsed = time.monotonic() - start
            ps = subprocess.run(['ps', '-o', 'rss=', '-p', str(proc.pid)],
                                capture_output=True, text=True)
            try:
                rss_kib = int(ps.stdout.strip())
            except ValueError:
                rss_kib = 0
            peak_rss_kib = max(peak_rss_kib, rss_kib)
            if rss_kib > 1_048_576 or elapsed > 30:
                proc.kill()
                proc.communicate()
                raise RuntimeError(f'child cap exceeded: rss_kib={rss_kib}, elapsed={elapsed}, argv={argv}')
    elapsed = time.monotonic() - start
    if elapsed > 30:
        raise RuntimeError(f'child elapsed cap exceeded: {elapsed}, argv={argv}')
    return gate, proc.returncode, stdout, stderr, elapsed, peak_rss_kib

def run_cell(results, role, suite, name, argv, env=None, artifact=None):
    key = f'{role}/{suite}/{name}'
    if key in results['cells']:
        return results['cells'][key]
    gate, code, out, err, elapsed, rss = guarded(argv, env)
    base = ROOT / 'raw' / suite / role
    base.mkdir(parents=True, exist_ok=True)
    stem = base / name
    (base / (name + '.stdout')).write_bytes(out)
    (base / (name + '.stderr')).write_bytes(err)
    art = artifact.read_bytes() if artifact and artifact.exists() else None
    rec = {'role': role, 'suite': suite, 'name': name, 'argv': [str(x) for x in argv],
           'env_LEAN_PATH': env.get('LEAN_PATH') if env else None,
           'admission': gate, 'exit_code': code, 'elapsed_s': elapsed,
           'sampled_peak_rss_kib': rss,
           'stdout_sha256': sha(out), 'stderr_sha256': sha(err),
           'stdout_bytes': len(out), 'stderr_bytes': len(err),
           'artifact': str(artifact.relative_to(ROOT)) if art is not None else None,
           'artifact_sha256': sha(art) if art is not None else None,
           'artifact_bytes': len(art) if art is not None else None}
    results['cells'][key] = rec
    (ROOT / 'results.json').write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
    print(key, code, len(out), len(err), round(gate['reclaimable_percent'], 2), gate['disk_free_bytes'], flush=True)
    return rec

def run_r444(results, role, lean):
    for case in CASES:
        target = ROOT / 'raw' / 'r444' / role / case / 'Probe.olean'
        target.parent.mkdir(parents=True, exist_ok=True)
        compile_argv = [str(lean), '--json', '-o', str(target.relative_to(ROOT)),
                        f'support/r444/{case}/Probe.lean']
        run_cell(results, role, 'r444', case, compile_argv, artifact=target)
        if case != 'd':
            env = os.environ.copy()
            env['LEAN_PATH'] = str(target.parent)
            run_cell(results, role, 'r444', case + '-consumer',
                     [str(lean), '--json', 'support/r444/query/Query.lean'], env=env)
    a = ROOT / 'raw' / 'r444' / role / 'a' / 'Probe.olean'
    first = ROOT / 'raw' / 'r444' / role / 'a-first.olean'
    if not first.exists():
        first.write_bytes(a.read_bytes())
    run_cell(results, role, 'r444', 'a-repeat',
             [str(lean), '--json', '-o', str(a.relative_to(ROOT)), 'support/r444/a/Probe.lean'], artifact=a)
    other = ROOT / 'raw' / 'r444' / role / 'a-output-only' / 'Probe.olean'
    other.parent.mkdir(parents=True, exist_ok=True)
    run_cell(results, role, 'r444', 'a-output-only',
             [str(lean), '--json', '-o', str(other.relative_to(ROOT)), 'support/r444/a/Probe.lean'], artifact=other)

def run_r448(results, role, lean):
    for name, (opts, json_mode) in FORMAT_OPTIONS.items():
        argv = [str(lean)]
        if json_mode:
            argv.append('--json')
        argv.extend('-D' + opt for opt in opts)
        argv.append('support/r448/Format.lean')
        run_cell(results, role, 'r448', name, argv)

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--role', choices=TOOLS)
    args = ap.parse_args()
    results_path = ROOT / 'results.json'
    results = json.loads(results_path.read_text()) if results_path.exists() else {'schema': 1, 'tools': {}, 'cells': {}}
    for role in ((args.role,) if args.role else TOOLS):
        lean = TOOLS[role]
        assert sha(lean.read_bytes()) == TOOL_SHA[role]
        version = subprocess.check_output([str(lean), '--version'], text=True).strip()
        results['tools'][role] = {'executable': str(lean), 'sha256': TOOL_SHA[role], 'version': version}
        results_path.write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
        run_r444(results, role, lean)
        run_r448(results, role, lean)

if __name__ == '__main__':
    main()
