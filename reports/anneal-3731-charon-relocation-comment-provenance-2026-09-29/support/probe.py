#!/usr/bin/env python3
"""Pinned, offline Charon/Aeneas path and comment identity probe."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
TOOLS = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RUST = TOOLS / 'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
CHARON = TOOLS / 'bin/charon'
AENEAS = TOOLS / 'bin/aeneas'
BASE = 'pub fn bump(x: u32) -> u32 { x.wrapping_add(1) }\n'
COMMENT = BASE + '// Inert fixture note after the function.\n'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(argv, env):
    p = subprocess.run([str(x) for x in argv], cwd=HERE, env=env,
                       capture_output=True, text=True, timeout=30)
    if p.returncode:
        raise RuntimeError(f'{argv}: exit {p.returncode}: {p.stderr}')
    return {'returncode': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr}


def canonical(value):
    if isinstance(value, dict):
        return {k: canonical(v) for k, v in value.items()}
    if isinstance(value, list):
        return [canonical(v) for v in value]
    return value


def diff(a, b, path='$'):
    if type(a) is not type(b):
        return [path]
    if isinstance(a, dict):
        return sum((diff(a[k], b[k], f'{path}.{k}') for k in a.keys() & b.keys()), []) + [f'{path}.{k}' for k in a.keys() ^ b.keys()]
    if isinstance(a, list):
        if len(a) != len(b):
            return [path + '.length']
        return sum((diff(x, y, f'{path}[{i}]') for i, (x, y) in enumerate(zip(a, b))), [])
    return [] if a == b else [path]


def normalized(doc):
    doc = canonical(doc)
    t = doc['translated']
    t['options']['dest_file'] = '<DEST>'
    for key in ('item_names', 'short_names', 'assoc_item_names'):
        t[key].sort(key=lambda entry: json.dumps(entry['key'], sort_keys=True))
    return doc


def main():
    assert sha(CHARON.read_bytes()) == '51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b'
    assert sha(AENEAS.read_bytes()) == 'f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03'
    env = dict(os.environ)
    env.update(RUSTUP_HOME=str(TOOLS / 'rustup'), CARGO_HOME=str(TOOLS / 'cargo'),
               CHARON_TOOLCHAIN_IS_IN_PATH='1', CARGO_NET_OFFLINE='true',
               PATH=os.pathsep.join((str(RUST), str(TOOLS / 'bin'), env.get('PATH', ''))),
               DYLD_LIBRARY_PATH=os.pathsep.join((str(RUST.parent / 'lib'),
                   str(RUST.parent / 'lib/rustlib/aarch64-apple-darwin/lib'),
                   env.get('DYLD_LIBRARY_PATH', ''))))
    for owned in (HERE / 'work', HERE / 'artifacts'):
        if owned.exists():
            shutil.rmtree(owned)
    result = {'tools': {'charon_sha256': sha(CHARON.read_bytes()),
                        'aeneas_sha256': sha(AENEAS.read_bytes()),
                        'rustc': run([RUST / 'rustc', '--version', '--verbose'], env)['stdout']},
              'cases': {}}
    docs = {}
    for name, source in [('origin', BASE), ('relocated', BASE), ('comment', COMMENT), ('repeat', BASE)]:
        root = HERE / 'work' / ('other-root' if name == 'relocated' else 'origin-root')
        src = root / 'src/lib.rs'
        src.parent.mkdir(parents=True, exist_ok=True)
        src.write_text(source)
        out = HERE / 'artifacts' / name
        out.mkdir(parents=True, exist_ok=True)
        llbc = out / 'probe.llbc'
        lean = out / 'lean'
        lean.mkdir(exist_ok=True)
        command = [CHARON, 'rustc', '--preset', 'aeneas', '--dest-file', llbc,
                   '--', src, '--crate-type', 'lib', '--crate-name', 'probe', '--edition', '2021']
        c = run(command, env)
        doc = json.loads(llbc.read_text())
        if doc['has_errors']:
            raise RuntimeError(f'{name}: Charon has_errors=true')
        a = run([AENEAS, '-backend', 'lean', '-dest', lean,
                 '-no-progress-bar', '-sequential', llbc], env)
        files = {p.name: {'sha256': sha(p.read_bytes()), 'bytes': p.stat().st_size}
                 for p in sorted(lean.iterdir()) if p.is_file()}
        result['cases'][name] = {'source_sha256': sha(src.read_bytes()),
            'source_bytes': len(src.read_bytes()), 'llbc_sha256': sha(llbc.read_bytes()),
            'llbc_bytes': llbc.stat().st_size, 'has_errors': doc['has_errors'],
            'charon': c, 'aeneas': a, 'lean_files': files,
            'local_file': next(f for f in doc['translated']['files'] if f['crate_name'] == 'probe')}
        docs[name] = normalized(doc)
    result['normalized_diff_paths'] = {
        'origin_relocated': sorted(diff(docs['origin'], docs['relocated'])),
        'origin_comment': sorted(diff(docs['origin'], docs['comment'])),
        'origin_repeat': sorted(diff(docs['origin'], docs['repeat']))}
    result['lean_equal'] = {
        pair: result['cases'][left]['lean_files'] == result['cases'][right]['lean_files']
        for pair, left, right in [('origin_relocated','origin','relocated'),
                                  ('origin_comment','origin','comment'),
                                  ('origin_repeat','origin','repeat')]}
    (HERE / 'results.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'normalized_diff_paths': result['normalized_diff_paths'],
                      'lean_equal': result['lean_equal']}, indent=2))


if __name__ == '__main__':
    main()
