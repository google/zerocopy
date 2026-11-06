#!/usr/bin/env python3
"""Small no-download Lake pruning and interactive-extension matrix."""
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
WORK = HERE / 'work'
HARNESS = REPORTS / 'anneal-3730-lean-uri-history-import-boundaries-2026-09-29/support/probe.py'
spec = importlib.util.spec_from_file_location('cached_uri_harness', HARNESS)
harness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(harness)
LEAN = harness.LEAN
LAKE = harness.LAKE
ENV = dict(harness.ENV, LAKE_ARTIFACT_CACHE='false', LAKE_CACHE_DIR='')
ENV['PATH'] = str(LEAN.parent) + os.pathsep + ENV.get('PATH', '')
COMMANDS = []


def sha(data):
    if isinstance(data, Path):
        data = data.read_bytes()
    if isinstance(data, str):
        data = data.encode()
    return hashlib.sha256(data).hexdigest()


def command(label, args, cwd, env=None, timeout=35):
    begin = time.monotonic()
    p = subprocess.run([str(x) for x in args], cwd=cwd, env=env or ENV,
                       capture_output=True, text=True, timeout=timeout)
    row = dict(label=label, argv=[str(x) for x in args], cwd=str(cwd),
               rc=p.returncode, stdout=p.stdout, stderr=p.stderr,
               seconds=round(time.monotonic()-begin, 3))
    COMMANDS.append(row)
    return row


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(data)


def fixture():
    producer = WORK / 'producer'
    consumer = WORK / 'consumer'
    producer.mkdir(parents=True)
    consumer.mkdir()
    write(producer/'lakefile.toml', 'name = "prune_producer"\n[[lean_lib]]\nname = "Base"\n[[lean_lib]]\nname = "Extra"\n[[lean_lib]]\nname = "Macro"\n[[lean_lib]]\nname = "Plugin"\n')
    write(consumer/'lakefile.toml', 'name = "prune_consumer"\n[[require]]\nname = "prune_producer"\npath = "../producer"\n')
    for directory in (producer, consumer):
        write(directory/'lean-toolchain', 'leanprover/lean4:v4.30.0-rc2\n')
    write(producer/'Base.lean', 'def selected : Nat := 7\n')
    write(producer/'Extra.lean', 'import Base\ndef extra : Nat := selected + 1\n')
    write(producer/'Macro.lean', 'import Lean\nsyntax "new_tac" : tactic\nmacro_rules | `(tactic| new_tac) => `(tactic| decide)\n')
    write(producer/'Plugin.lean', 'import Lean\ninitialize do\n  let p := (← IO.getEnv "PLUGIN_MARKER").getD ""\n  if !p.isEmpty then IO.FS.writeFile p "plugin-loaded"\n')
    write(consumer/'ProofBase.lean', 'import Base\ntheorem baseProof : selected = 7 := by\n  rfl\n')
    write(consumer/'ProofTactic.lean', 'import Base\ntheorem tacticProof : selected = 7 := by\n  decide\n')
    write(consumer/'ProofExtra.lean', 'import Extra\ntheorem extraProof : extra = 8 := by\n  decide\n')
    write(consumer/'ProofMacro.lean', 'import Base\nimport Macro\ntheorem macroProof : selected = 7 := by\n  new_tac\n')
    return producer, consumer


def artifacts(producer):
    base = producer/'.lake/build'
    return {
        'base_olean': base/'lib/lean/Base.olean',
        'extra_olean': base/'lib/lean/Extra.olean',
        'macro_olean': base/'lib/lean/Macro.olean',
        'plugin_olean': base/'lib/lean/Plugin.olean',
        'plugin_dylib': next((base/'lib/lean').glob('*Plugin.dylib')),
    }


def inventory(producer):
    base = producer/'.lake/build'
    rows = {}
    for path in base.rglob('*'):
        if path.is_file():
            rows[path.relative_to(base).as_posix()] = {'bytes': path.stat().st_size,
                                                        'sha256': sha(path)}
    return dict(files=rows, total_bytes=sum(x['bytes'] for x in rows.values()),
                file_count=len(rows))


def run_proofs(consumer, plugin_path, label):
    out = {}
    for name in ('ProofBase.lean', 'ProofTactic.lean', 'ProofExtra.lean', 'ProofMacro.lean'):
        out[name] = command(label+'-'+name,
            [LAKE, '--keep-toolchain', '--no-cache', 'env', LEAN, '--json', name], consumer)
    marker = WORK / (label+'-plugin-marker.txt')
    marker.unlink(missing_ok=True)
    plugin_env = dict(ENV, PLUGIN_MARKER=str(marker))
    out['plugin_load'] = command(label+'-plugin',
        [LAKE, '--keep-toolchain', '--no-cache', 'env', LEAN,
         '--plugin='+str(plugin_path), 'ProofBase.lean'], consumer, plugin_env)
    out['plugin_marker'] = marker.read_text() if marker.exists() else None
    return out


def live_scratch(consumer):
    server = harness.Server('pruned-scratch', consumer, 'lake-serve')
    out = []
    try:
        for label, text in (
            ('base', 'import Base\ntheorem scratch : selected = 7 := by\n  exact ?_\n'),
            ('extra', 'import Extra\ntheorem scratch : extra = 8 := by\n  exact ?_\n'),
        ):
            uri = (consumer/(label+'-Scratch.lean')).as_uri()
            wait = harness.open_uri(server, uri, text)
            goal = harness.goal_uri(server, uri, 2, 2)
            out.append(dict(label=label, uri=uri, text=text, wait=wait, goal=goal,
                            diagnostics=server.diags.get(uri), physical_exists=(consumer/(label+'-Scratch.lean')).exists()))
            server.send(dict(jsonrpc='2.0', method='textDocument/didClose',
                             params={'textDocument': {'uri': uri}}))
    finally:
        server.stop()
    return out


def main():
    assert LEAN.is_file() and LAKE.is_file()
    disk = shutil.disk_usage(HERE)
    assert disk.free >= 5 * 1024**3, '5 GiB disk free required'
    pressure = subprocess.run(['memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
    found = re.search(r'System-wide memory free percentage: (\d+)%', pressure.stdout)
    assert found and int(found.group(1)) >= 25, '25% memory free required'
    if WORK.exists():
        shutil.rmtree(WORK)
    producer, consumer = fixture()
    build = command('build-full', [LAKE,'--keep-toolchain','--no-cache','build',
                                   'Base','Extra','Macro','+Plugin:dynlib'], producer, timeout=80)
    assert build['rc'] == 0, build
    art = artifacts(producer)
    assert all(path.is_file() for path in art.values())
    before = inventory(producer)
    full = run_proofs(consumer, art['plugin_dylib'], 'full')
    assert all(full[name]['rc'] == 0 for name in ('ProofBase.lean','ProofTactic.lean','ProofExtra.lean','ProofMacro.lean','plugin_load'))
    assert full['plugin_marker'] == 'plugin-loaded'
    removed = {}
    for key in ('extra_olean','macro_olean','plugin_dylib'):
        path = art[key]
        removed[key] = dict(path=str(path), bytes=path.stat().st_size, sha256=sha(path))
        path.unlink()
    after = inventory(producer)
    pruned = run_proofs(consumer, art['plugin_dylib'], 'pruned')
    no_build = {
        'extra': command('pruned-no-build-extra',
            [LAKE,'--keep-toolchain','--no-cache','--no-build','build','Extra'], producer),
        'macro': command('pruned-no-build-macro',
            [LAKE,'--keep-toolchain','--no-cache','--no-build','build','Macro'], producer),
    }
    assert no_build['extra']['rc'] != 0 and no_build['macro']['rc'] != 0
    after_no_build = inventory(producer)
    live = live_scratch(consumer)
    after_live = inventory(producer)
    assert pruned['ProofBase.lean']['rc'] == 0
    assert pruned['ProofTactic.lean']['rc'] == 0
    assert pruned['ProofExtra.lean']['rc'] != 0
    assert pruned['ProofMacro.lean']['rc'] != 0
    assert pruned['plugin_load']['rc'] != 0 and pruned['plugin_marker'] is None
    assert before['total_bytes'] - after['total_bytes'] == sum(x['bytes'] for x in removed.values())
    assert live[0]['wait'].get('result') == {} and '⊢ selected = 7' in str(live[0]['goal'])
    assert live[1]['wait'].get('result') == {} and '⊢ extra = 8' in str(live[1]['goal'])
    assert art['extra_olean'].is_file()
    assert not art['macro_olean'].exists() and not art['plugin_dylib'].exists()
    result = dict(subject=dict(lean_sha256=sha(LEAN), lake_sha256=sha(LAKE),
                               probe_sha256=sha(Path(__file__)),
                               cached_harness_sha256=sha(HARNESS),
                               host_free_percent=int(found.group(1)),
                               disk_free_bytes=disk.free),
                  build=build, before=before, removed=removed, after=after,
                  full=full, pruned=pruned, no_build=no_build,
                  after_no_build=after_no_build,
                  live_scratch=live, after_live=after_live,
                  commands=COMMANDS, wire_events=harness.prior.EVENTS)
    (HERE/'results.json').write_text(json.dumps(result, indent=2, ensure_ascii=False)+'\n')
    print(json.dumps({'full_bytes': before['total_bytes'],
                      'pruned_bytes': after['total_bytes'],
                      'removed_bytes': before['total_bytes']-after['total_bytes']}, sort_keys=True))


if __name__ == '__main__':
    main()
