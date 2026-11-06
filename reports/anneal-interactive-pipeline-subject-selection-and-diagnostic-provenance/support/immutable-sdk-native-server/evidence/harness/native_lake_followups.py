"""Small consumer-only invalidation and native-library negative cases.

Only --prepare writes scratch fixtures. Each --run-* stage uses the existing
guarded real_sdk_lake.invoke; execute stages serially via the root controller.
"""

import argparse
from pathlib import Path

from native_lake import PLUGIN, SMOKE, tiny_smoke
from probes import ROOT
from real_sdk_lake import invoke


def prepare_invalidation() -> Path:
    return tiny_smoke('native-lake-invalidation')


def prepare_bad_plugin() -> Path:
    w = tiny_smoke('native-lake-bad-plugin')
    bad = w / 'invalid-plugin.dylib'
    bad.write_bytes(b'not a Mach-O dynamic library\n')
    lakefile = w / 'lakefile.lean'
    lakefile.write_text(lakefile.read_text().replace(str(PLUGIN), str(bad)))
    return w


def build(w: Path, label: str):
    return invoke(label, ['lake', '--keep-toolchain', '--no-cache', '--verbose', 'build', '+Smoke:olean'], w)


def run_noop(w: Path):
    output = w / '.lake/build/lib/lean/Smoke.olean'
    if not output.is_file():
        raise RuntimeError('Run baseline first; no-op needs an existing local olean')
    before = (output.stat().st_mtime_ns, output.stat().st_size)
    result = build(w, 'native-lake-followup-noop')
    after = (output.stat().st_mtime_ns, output.stat().st_size)
    print('NOOP_OUTPUT', before, after, 'unchanged=', before == after, flush=True)
    return result


def run_edit(w: Path):
    (w / 'Smoke.lean').write_text(SMOKE + '\ndef privateVersion : Nat := 2\n')
    return build(w, 'native-lake-followup-edit')


def run_delete(w: Path):
    output = w / '.lake/build/lib/lean/Smoke.olean'
    if not output.is_file():
        raise RuntimeError('Run baseline and edit first; output is missing')
    output.unlink()
    return build(w, 'native-lake-followup-delete-output')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('stage', choices=['prepare', 'baseline', 'noop', 'edit', 'delete-output',
                                      'prepare-bad-plugin', 'bad-plugin'])
    ns = ap.parse_args()
    if ns.stage == 'prepare':
        print(prepare_invalidation())
    elif ns.stage == 'prepare-bad-plugin':
        print(prepare_bad_plugin())
    elif ns.stage == 'bad-plugin':
        w = ROOT / 'work/native-lake-bad-plugin'
        invoke('native-lake-followup-bad-target',
               ['lake', '--keep-toolchain', '--no-cache', 'build', 'aeneasMetaPlugin'], w)
        build(w, 'native-lake-followup-bad-plugin')
    else:
        w = ROOT / 'work/native-lake-invalidation'
        if ns.stage == 'baseline':
            build(w, 'native-lake-followup-baseline')
        elif ns.stage == 'noop':
            run_noop(w)
        elif ns.stage == 'edit':
            run_edit(w)
        elif ns.stage == 'delete-output':
            run_delete(w)
