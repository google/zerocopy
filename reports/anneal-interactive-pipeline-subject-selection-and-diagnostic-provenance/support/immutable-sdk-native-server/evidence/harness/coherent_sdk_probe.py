#!/usr/bin/env python3
"""Guarded tiny test of a read-only SDK view with copied Lean *and* Lake."""

import hashlib
import json
import os
import shutil
import stat
import time
from pathlib import Path

from guard import ROOT, run
from probes import AENEAS, RC2, environment, snapshot
from native_lake import PLUGIN, plugin_config, SMOKE

SDK = ROOT / 'sdk-install'
BASE = ROOT / 'coherent-sdk-probe'
RECORD = ROOT / 'coherent-sdk-results.jsonl'


def emit(row):
    with RECORD.open('a') as out:
        out.write(json.dumps(row, sort_keys=True) + '\n')
    print('COHERENT_SDK', json.dumps(row, sort_keys=True), flush=True)


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as src:
        while block := src.read(1024 * 1024):
            h.update(block)
    return h.hexdigest()


def make_view(view):
    if view.exists():
        raise RuntimeError(f'refusing overwrite: {view}')
    (view / 'bin').mkdir(parents=True)
    for path in SDK.iterdir():
        if path.name != 'bin':
            (view / path.name).symlink_to(path,
                target_is_directory=path.is_dir())
    for path in (SDK / 'bin').iterdir():
        if path.name not in ('lean', 'lake'):
            (view / 'bin' / path.name).symlink_to(path,
                target_is_directory=path.is_dir())
    shutil.copy2(SDK / 'bin/lean', view / 'bin/lean')
    shutil.copy2(RC2 / 'bin/lake', view / 'bin/lake')
    for path in (view / 'bin', view):
        path.chmod(stat.S_IMODE(path.stat().st_mode) & ~0o222)


def make_consumer(work):
    work.mkdir()
    (work / 'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n')
    (work / 'lakefile.lean').write_text(plugin_config('coherent_sdk_smoke',
        '@[default_target] lean_lib Smoke where\n  roots := #[`Smoke]\n'))
    (work / 'Smoke.lean').write_text(SMOKE)


def call(label, view, work, args):
    env = environment(RC2, label, immutable=f'{view}:{SDK}:{AENEAS}:{RC2}')
    env['LEAN_SYSROOT'] = str(view)
    env['LAKE_OVERRIDE_LEAN'] = 'true'
    env['PATH'] = str(view / 'bin') + ':' + env['PATH']
    env['LEAN_SRC_PATH'] = json.loads(
        (ROOT / 'real-sdk-lsp-navigation-env.json').read_text())['LEAN_SRC_PATH']
    env['DYLD_PRINT_LIBRARIES'] = '1'
    record = run(label, [str(view / 'bin/lake'), '--keep-toolchain',
                         '--no-cache', *args], cwd=work, env=env,
                 timeout=90, rss_mib=1536)
    out = Path(record['stdout']).read_text(errors='replace')
    err = Path(record['stderr']).read_text(errors='replace')
    trace = ROOT / 'records' / (label + '.events.jsonl')
    events = [json.loads(s) for s in trace.read_text().splitlines()] \
        if trace.exists() else []
    row = {'label': label, 'exit': record['exit'], 'abort': record['abort'],
           'elapsed_s': record['elapsed_s'],
           'peak_sampled_rss_mib': round(max(s['rss_kib'] for s in record['samples']) / 1024, 2),
           'min_memory_free_pct': min(s['memory_free_pct'] for s in record['samples']),
           'min_disk_free_gib': round(min(s['disk_free_bytes'] for s in record['samples']) / 1024**3, 2),
           'blocked_mutations': [e for e in events
               if e['kind'] == 'mutation' and e['blocked']],
           'network_attempts': [e for e in events if e['kind'] == 'network'],
           # Lake relays compiler dyld output to stdout on this toolchain.
           'dyld_native_lines': [line for line in (out + '\n' + err).splitlines()
               if 'libaeneas_AeneasMeta.dylib' in line],
           'stdout_tail': out[-3000:], 'stderr_tail': err[-1200:],
           'stdout_file': record['stdout'], 'stderr_file': record['stderr']}
    emit(row)
    return row


def main():
    tag = time.strftime('%Y%m%d-%H%M%S')
    base = BASE / tag
    base.mkdir(parents=True)
    view, work = base / 'view', base / 'consumer'
    make_view(view)
    make_consumer(work)
    roots = (view, SDK, AENEAS)
    before = [snapshot(tag + f'-before-{i}', root=p, content=(i != 2))
              for i, p in enumerate(roots)]
    important = (SDK / 'bin/lean', RC2 / 'bin/lake', PLUGIN,
                 AENEAS / 'backends/lean/.lake/build/lib/lean/AeneasMeta/Saturate/Tactic.olean')
    digests_before = {str(p): digest(p) for p in important}
    prefix = call(tag + '-prefix', view, work, ['env', 'lean', '--print-prefix'])
    if prefix['exit'] == 0 and not prefix['abort']:
        build = call(tag + '-build', view, work,
                     ['--verbose', 'build', '+Smoke:olean'])
        if build['exit'] == 0 and not build['abort']:
            call(tag + '-setup', view, work,
                 ['setup-file', 'Smoke.lean'])
    after = [snapshot(tag + f'-after-{i}', root=p, content=(i != 2))
             for i, p in enumerate(roots)]
    digests_after = {str(p): digest(p) for p in important}
    emit({'label': tag + '-integrity',
          'view_and_sdk_content_metadata_unchanged': before[:2] == after[:2],
          'archive_tree_metadata_unchanged': before[2] == after[2],
          'selected_shared_artifact_hashes_unchanged': digests_before == digests_after,
          'copied_lean_bytes': (view / 'bin/lean').stat().st_size,
          'copied_lake_bytes': (view / 'bin/lake').stat().st_size,
          'view': str(view), 'consumer': str(work)})


if __name__ == '__main__':
    main()
