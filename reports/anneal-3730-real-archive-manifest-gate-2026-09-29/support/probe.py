#!/usr/bin/env python3
"""Bounded offline Lake component control; not an Anneal archive test."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

BASE = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
LAKE = BASE / 'lake'
TOOLCHAIN = 'leanprover/lean4:v4.30.0-rc2'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(root):
    return {str(p.relative_to(root)): [p.stat().st_size, digest(p)]
            for p in sorted(root.rglob('*')) if p.is_file()}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', type=Path, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    if work.exists():
        raise SystemExit('work path must not exist')
    if shutil.disk_usage(work.parent).free < 2 * 1024**3:
        raise SystemExit('need 2 GiB free disk preflight')
    if not LAKE.is_file() or not Path('/usr/bin/sandbox-exec').is_file():
        raise SystemExit('pinned Lake or macOS sandbox-exec unavailable')
    work.mkdir(parents=True)
    home = work / 'empty-home'; home.mkdir()
    cache = work / 'empty-cache'; cache.mkdir()
    dep = work / 'producer'; dep.mkdir()
    (dep / 'lean-toolchain').write_text(TOOLCHAIN + '\n')
    (dep / 'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n')
    (dep / 'Dep.lean').write_text('def depValue : Nat := 7\n')
    env = dict(os.environ)
    env.update(HOME=str(home), XDG_CACHE_HOME=str(cache), LAKE_CACHE_DIR='',
               LAKE_ARTIFACT_CACHE='false', LEAN_NUM_THREADS='1',
               ELAN_TOOLCHAIN=TOOLCHAIN, ELAN_HOME=str(BASE.parents[2]))
    entries = []

    def run(label, cwd, args, guarded=False):
        argv = [str(LAKE), '--keep-toolchain', *args]
        if guarded:
            # Deny any attempted write to the prepared dependency and network.
            profile = '(version 1) (allow default) (deny network*) (deny file-write* (subpath "' + str(dep) + '"))'
            argv = ['/usr/bin/sandbox-exec', '-p', profile, *argv]
        start = time.monotonic()
        try:
            cp = subprocess.run(argv, cwd=cwd, env=env, text=True,
                                capture_output=True, timeout=35)
            result = dict(exit=cp.returncode, stdout=cp.stdout, stderr=cp.stderr)
        except subprocess.TimeoutExpired as exc:
            result = dict(exit='timeout', stdout=str(exc.stdout), stderr=str(exc.stderr))
        result.update(label=label, argv=argv, cwd=str(cwd), seconds=round(time.monotonic()-start, 3))
        entries.append(result)
        return result

    build = run('prepare-producer', dep, ['build', 'Dep'])
    if build['exit'] != 0:
        raise SystemExit('producer preparation failed: ' + build['stderr'])
    manifest = {
        'version': '1.2.0', 'packagesDir': '.lake/packages',
        'packages': [{'type': 'path', 'scope': '', 'name': 'probe_dep',
                      'manifestFile': 'lake-manifest.json', 'inherited': False,
                      'dir': '../producer', 'configFile': 'lakefile.lean'}],
        'name': 'probe_consumer', 'lakeDir': '.lake', 'fixedToolchain': False}
    # Preparation includes the dependency's configuration products required by
    # this consumer shape. A bare `lake build Dep` is not a complete archive.
    primer = work / 'primer'; primer.mkdir()
    (primer / 'lean-toolchain').write_text(TOOLCHAIN + '\n')
    (primer / 'lakefile.lean').write_text('import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\npackage probe_consumer\n@[default_target]\nlean_lib Generated\n')
    (primer / 'Generated.lean').write_text('import Dep\ntheorem firstGoal : depValue + 1 = 8 := by decide\n#print axioms firstGoal\n')
    (primer / 'lake-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    prime = run('prime-consumer', primer, ['build', 'Generated'])
    if prime['exit'] != 0:
        raise SystemExit('consumer preparation failed: ' + prime['stderr'])
    before = inventory(dep)
    consumers = {}
    for label, has_manifest in [('complete', True), ('missing', False)]:
        c = work / label; c.mkdir()
        (c / 'lean-toolchain').write_text(TOOLCHAIN + '\n')
        (c / 'lakefile.lean').write_text('import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\npackage probe_consumer\n@[default_target]\nlean_lib Generated\n')
        (c / 'Generated.lean').write_text('import Dep\ntheorem firstGoal : depValue + 1 = 8 := by decide\n#print axioms firstGoal\n')
        if has_manifest:
            (c / 'lake-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        consumers[label] = c
        run(label+'-setup', c, ['setup-file', 'Generated.lean'], guarded=True)
        run(label+'-batch', c, ['env', 'lean', '--json', 'Generated.lean'], guarded=True)
    after = inventory(dep)
    # Moving the sole prepared producer out of the manifest's target path is a
    # negative control; no compiled dependency remains accessible there.
    dep.rename(work / 'producer-removed')
    run('removed-setup', consumers['complete'], ['setup-file', 'Generated.lean'], guarded=False)
    output = {
        'subject': 'synthetic local Lake producer/consumer, not Anneal archive',
        'lake_sha256': digest(LAKE), 'toolchain': TOOLCHAIN,
        'work': str(work), 'environment': {k: env[k] for k in
            ['HOME','XDG_CACHE_HOME','LAKE_CACHE_DIR','LAKE_ARTIFACT_CACHE','LEAN_NUM_THREADS','ELAN_TOOLCHAIN','ELAN_HOME']},
        'producer_inventory_before': before, 'producer_inventory_after': after,
        'producer_unchanged': before == after, 'commands': entries,
    }
    rendered = json.dumps(output, indent=2)
    rendered = rendered.replace(str(work), '$WORK').replace(str(BASE), '$TOOLCHAIN_BIN')
    (Path(__file__).parent / 'results.json').write_text(rendered + '\n')
    assert before == after, 'producer changed under sandboxed consumers'
    by_label = {c['label']: c for c in entries}
    assert by_label['complete-setup']['exit'] == 0 and by_label['complete-batch']['exit'] == 0
    assert "'firstGoal' does not depend on any axioms" in by_label['complete-batch']['stdout']
    assert by_label['missing-setup']['exit'] != 0 and by_label['missing-batch']['exit'] != 0
    assert by_label['removed-setup']['exit'] != 0
    print('PASS: complete/missing/removed producer controls; results.json written')


if __name__ == '__main__':
    main()
