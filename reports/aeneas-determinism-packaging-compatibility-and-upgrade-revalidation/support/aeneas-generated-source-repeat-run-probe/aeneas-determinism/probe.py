#!/usr/bin/env python3
"""Run a small, bounded Aeneas byte-determinism probe on existing LLBC."""

import hashlib
import json
import pathlib
import shutil
import subprocess
import time


ROOT = pathlib.Path.cwd()
SCRATCH = pathlib.Path('.anneal-local-tools/scratch/aeneas-determinism')
INPUT = pathlib.Path('.anneal-local-tools/scratch/translation-goldens/probe.llbc')
RUNS = SCRATCH / 'runs'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(label, dest):
    dest.mkdir(parents=True, exist_ok=True)
    command = ['aeneas', '-backend', 'lean', '-dest', str(dest),
               '-no-progress-bar', str(INPUT)]
    started_ns = time.time_ns()
    result = subprocess.run(command, capture_output=True, text=True, timeout=20)
    finished_ns = time.time_ns()
    snapshot = RUNS / label
    snapshot.mkdir(parents=True, exist_ok=False)
    (snapshot / 'stdout.txt').write_text(result.stdout)
    (snapshot / 'stderr.txt').write_text(result.stderr)
    files = []
    for path in sorted(dest.rglob('*')):
        if path.is_file():
            relative = path.relative_to(dest)
            copied = snapshot / relative
            copied.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, copied)
            st = path.stat()
            files.append({'path': str(relative), 'bytes': st.st_size,
                          'sha256': digest(path), 'mtime_ns': st.st_mtime_ns})
    return {'label': label, 'argv': command, 'returncode': result.returncode,
            'started_ns': started_ns, 'finished_ns': finished_ns,
            'stdout_sha256': digest(snapshot / 'stdout.txt'),
            'stderr_sha256': digest(snapshot / 'stderr.txt'), 'files': files}


def main():
    assert INPUT.is_file()
    RUNS.mkdir(parents=True, exist_ok=False)
    records = []
    same = SCRATCH / 'same-dest'
    for index in range(1, 6):
        records.append(run(f'same-{index}', same))
    for index in range(1, 6):
        records.append(run(f'fresh-{index}', SCRATCH / f'fresh-dest-{index}'))
    manifest = {'input': str(INPUT), 'input_bytes': INPUT.stat().st_size,
                'input_sha256': digest(INPUT), 'records': records}
    (SCRATCH / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    for record in records:
        print(record['label'], record['returncode'],
              [(f['path'], f['bytes'], f['sha256'], f['mtime_ns'])
               for f in record['files']])


if __name__ == '__main__':
    main()
